-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.DispatchArmPreservation
import SeLe4n.Kernel.SchedContext.BindingAffinity
import SeLe4n.Kernel.IPC.Invariant.CancelAllFrame
import SeLe4n.Kernel.IPC.Invariant.CancellationBundle

/-!
# The scheduling links a final delete carries

A final delete retires a scheduling context on the context's own links: bound
to no thread, lent from none, heading no reply stack.  That reading is the
whole truth only on a state where every other reference to a context is
answered by the context itself:

* **the timeout budgets** (`allTimeoutBudgetsNone`): no thread holds one;
* **the binding pair** (`schedContextBindingConsistent`): a thread bound to a
  context, as its own or on loan, is the thread the context names, and a context
  naming a thread is bound to it (the thread-side half the coverage proofs read,
  `schedContextBindingBidirectional`, is its consequence, with the lender's
  loan record from the IPC bundle);
* **the replenishment pair** (`replenishQueueEntriesBound_smp`,
  `replenishQueueAffinityConsistent_smp`): a context a core's replenishment
  queue holds is bound to a thread, and is queued on that thread's home core.

This module carries those invariants (`schedContextLinkInvariant`) along every
step of the delete: each finalisation step, the slot delete, the page teardown,
a thread slot's copy and the retire.  Most steps write none of what the
invariants read — a thread's binding codes, budget and affinity, a context's
bound-thread code, the replenishment queues — and keep them by a frame
(`SchedLinkFrame`); the two that do, a context's release of its holder and a
reply's caller cancel with its loan returned, are proven on their own.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

-- ============================================================================
-- §1  What the invariants read
-- ============================================================================

/-- **The invariants the scheduling context's own-link retire reads**, carried
along the whole delete chain. -/
structure schedContextLinkInvariant (st : SystemState) : Prop where
  budgets : allTimeoutBudgetsNone st
  binding : schedContextBindingConsistent st
  replenishBound : replenishQueueEntriesBound_smp st
  replenishAffinity : replenishQueueAffinityConsistent_smp st
  /-- WS-ZA ZA6.3: every core's release queue agrees with the contexts' links. -/
  refined : st.releaseQueueRefined

/-- **What the budget and affinity invariants read of an object**: a thread's
timeout budget and core affinity; nothing of any other kind. -/
def tcbSchedAuxOf : Option KernelObject → Option (Option SeLe4n.SchedContextId × Option CoreId)
  | some (.tcb t) => some (t.timeoutBudget, t.cpuAffinity)
  | _ => none

/-- **What the binding invariants read of an object**: a thread's binding
codes, a scheduling context's bound-thread code. -/
def schedBindingLinksOf : Option KernelObject → Option ((Nat × Nat) ⊕ Nat)
  | some (.tcb t) => some (.inl (t.scBindingScCode, t.scBindingOwnerCode))
  | some (.schedContext sc) => some (.inr sc.boundThreadCode)
  | _ => none

/-- **What the release-queue agreement reads of an object**: a context's three
release fields; nothing of any other kind. -/
def schedReleaseOf : Option KernelObject → Option (Nat × Nat × Nat)
  | some (.schedContext sc) => some (sc.releaseNextCode, sc.releaseCoreCode, sc.releaseAt)
  | _ => none

/-- An object's release links, read off its release fields. -/
theorem objReleaseLinkOn_eq_schedReleaseOf (o : Option KernelObject) (c : CoreId) :
    SystemState.objReleaseLinkOn o c =
      match schedReleaseOf o with
      | some (n, cc, a) => if cc = c.val + 1 then some (n, a) else none
      | none => none := by
  cases o with
  | none => rfl
  | some o => cases o <;> rfl

/-- An object's release links are read off its release fields. -/
theorem objReleaseLinkOn_of_schedReleaseOf {a b : Option KernelObject}
    (h : schedReleaseOf a = schedReleaseOf b) (c : CoreId) :
    SystemState.objReleaseLinkOn a c = SystemState.objReleaseLinkOn b c := by
  rw [objReleaseLinkOn_eq_schedReleaseOf, objReleaseLinkOn_eq_schedReleaseOf, h]

/-- **A step that writes nothing the scheduling-link invariants read**: every
key keeps its thread's budget, affinity and binding codes and its context's
bound-thread code and release fields, and the scheduler keeps every
release-queue slot. -/
structure SchedLinkFrame (st st' : SystemState) : Prop where
  aux : ∀ oid : SeLe4n.ObjId, tcbSchedAuxOf st'.objects[oid]? = tcbSchedAuxOf st.objects[oid]?
  binding : ∀ oid : SeLe4n.ObjId,
    schedBindingLinksOf st'.objects[oid]? = schedBindingLinksOf st.objects[oid]?
  release : ∀ oid : SeLe4n.ObjId, schedReleaseOf st'.objects[oid]? = schedReleaseOf st.objects[oid]?
  slots : st'.scheduler.releaseSlots = st.scheduler.releaseSlots

namespace SchedLinkFrame

theorem refl (st : SystemState) : SchedLinkFrame st st :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

theorem trans {a b c : SystemState} (h₁ : SchedLinkFrame a b) (h₂ : SchedLinkFrame b c) :
    SchedLinkFrame a c :=
  ⟨fun o => (h₂.aux o).trans (h₁.aux o), fun o => (h₂.binding o).trans (h₁.binding o),
    fun o => (h₂.release o).trans (h₁.release o), h₂.slots.trans h₁.slots⟩

/-- A frame step holds the release queues. -/
theorem releaseState {st st' : SystemState} (h : SchedLinkFrame st st') :
    SystemState.releaseStateAgree st' st :=
  ⟨.of_objReleaseLinkOn fun k c => objReleaseLinkOn_of_schedReleaseOf (h.release k) c, h.slots⟩

/-- ...so every core keeps its abstract release queue. -/
theorem replenish {st st' : SystemState} (h : SchedLinkFrame st st') (c : CoreId) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c :=
  h.releaseState.replenishQueueOnCore c

end SchedLinkFrame

-- ============================================================================
-- §2  Reading the projections back
-- ============================================================================

theorem tcbSchedAuxOf_tcb {o : Option KernelObject} {t : TCB}
    (h : tcbSchedAuxOf (some (.tcb t)) = tcbSchedAuxOf o) :
    ∃ u, o = some (.tcb u) ∧ u.timeoutBudget = t.timeoutBudget ∧ u.cpuAffinity = t.cpuAffinity := by
  cases o with
  | none => cases h
  | some o =>
    cases o <;> first | cases h | skip
    rename_i u
    simp only [tcbSchedAuxOf, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨u, rfl, h.1.symm, h.2.symm⟩

theorem schedBindingLinksOf_tcb {o : Option KernelObject} {t : TCB}
    (h : schedBindingLinksOf (some (.tcb t)) = schedBindingLinksOf o) :
    ∃ u, o = some (.tcb u) ∧ u.schedContextBinding = t.schedContextBinding := by
  cases o with
  | none => cases h
  | some o =>
    cases o <;> first | cases h | skip
    rename_i u
    simp only [schedBindingLinksOf, Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
    exact ⟨u, rfl, by simp [TCB.schedContextBinding, h.1, h.2]⟩

theorem schedBindingLinksOf_schedContext {o : Option KernelObject} {sc : SchedContext}
    (h : schedBindingLinksOf (some (.schedContext sc)) = schedBindingLinksOf o) :
    ∃ s, o = some (.schedContext s) ∧ s.boundThread = sc.boundThread := by
  cases o with
  | none => cases h
  | some o =>
    cases o <;> first | cases h | skip
    rename_i s
    simp only [schedBindingLinksOf, Option.some.injEq, Sum.inr.injEq] at h
    exact ⟨s, rfl, by simp [SchedContext.boundThread, h]⟩

/-- Two states agree on every binding projection. -/
def bindingLinksAgree (st st' : SystemState) : Prop :=
  ∀ oid : SeLe4n.ObjId, schedBindingLinksOf st'.objects[oid]? = schedBindingLinksOf st.objects[oid]?

/-- Two states agree on every budget and affinity projection. -/
def schedAuxAgree (st st' : SystemState) : Prop :=
  ∀ oid : SeLe4n.ObjId, tcbSchedAuxOf st'.objects[oid]? = tcbSchedAuxOf st.objects[oid]?

namespace bindingLinksAgree

variable {st st' : SystemState}

theorem symm (h : bindingLinksAgree st st') : bindingLinksAgree st' st := fun o => (h o).symm

/-- A thread after the step is a thread before it, with the same binding. -/
theorem tcb_back (h : bindingLinksAgree st st') {k : SeLe4n.ObjId} {t : TCB}
    (hk : st'.objects[k]? = some (.tcb t)) :
    ∃ u, st.objects[k]? = some (.tcb u) ∧ u.schedContextBinding = t.schedContextBinding := by
  have e := h k; rw [hk] at e; exact schedBindingLinksOf_tcb e

/-- A context after the step is a context before it, naming the same thread. -/
theorem sc_back (h : bindingLinksAgree st st') {k : SeLe4n.ObjId} {sc : SchedContext}
    (hk : st'.objects[k]? = some (.schedContext sc)) :
    ∃ s, st.objects[k]? = some (.schedContext s) ∧ s.boundThread = sc.boundThread := by
  have e := h k; rw [hk] at e; exact schedBindingLinksOf_schedContext e

theorem getSchedContext?_back (h : bindingLinksAgree st st') {s : SeLe4n.SchedContextId}
    {sc : SchedContext} (hk : st'.getSchedContext? s = some sc) :
    ∃ u, st.getSchedContext? s = some u ∧ u.boundThread = sc.boundThread := by
  obtain ⟨u, hu, e⟩ := h.sc_back ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hk)
  exact ⟨u, (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hu, e⟩

theorem trans {a b c : SystemState} (h₁ : bindingLinksAgree a b)
    (h₂ : bindingLinksAgree b c) : bindingLinksAgree a c := fun o => (h₂ o).trans (h₁ o)

theorem of_objects_eq {a b : SystemState} (h : b.objects = a.objects) :
    bindingLinksAgree a b := fun o => by rw [h]

/-- A thread read across a step agreeing on the bindings has the same binding
codes there, both ways. -/
theorem getTcb?_back {s s' : SystemState} (h : bindingLinksAgree s s')
    {v : SeLe4n.ThreadId} {t' : TCB} (ht : s'.getTcb? v = some t') :
    ∃ t, s.getTcb? v = some t ∧ t'.scBindingScCode = t.scBindingScCode ∧
      t'.scBindingOwnerCode = t.scBindingOwnerCode := by
  have e := h v.toObjId
  rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp ht] at e
  cases h0 : s.objects[v.toObjId]? with
  | none => rw [h0] at e; cases e
  | some o =>
    rw [h0] at e
    cases o with
    | tcb t =>
      simp only [schedBindingLinksOf, Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at e
      exact ⟨t, (SystemState.getTcb?_eq_some_iff _ _ _).mpr h0, e.1, e.2⟩
    | schedContext _ => cases e
    | _ => cases e

theorem getTcb?_fwd {s s' : SystemState} (h : bindingLinksAgree s s')
    {v : SeLe4n.ThreadId} {t : TCB} (ht : s.getTcb? v = some t) :
    ∃ t', s'.getTcb? v = some t' ∧ t'.scBindingScCode = t.scBindingScCode ∧
      t'.scBindingOwnerCode = t.scBindingOwnerCode := by
  have e := h v.toObjId
  rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp ht] at e
  cases h0 : s'.objects[v.toObjId]? with
  | none => rw [h0] at e; cases e
  | some o =>
    rw [h0] at e
    cases o with
    | tcb t' =>
      simp only [schedBindingLinksOf, Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at e
      exact ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h0, e.1, e.2⟩
    | schedContext _ => cases e
    | _ => cases e

/-- A context read after a step agreeing on the bindings is one before it,
bound to the same thread, both ways. -/
theorem getSchedContext?_fwd {s s' : SystemState} (h : bindingLinksAgree s s')
    {c : SeLe4n.SchedContextId} {sc : SchedContext} (hc : s.getSchedContext? c = some sc) :
    ∃ sc', s'.getSchedContext? c = some sc' ∧ sc'.boundThreadCode = sc.boundThreadCode := by
  have e := h c.toObjId
  rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mp hc] at e
  cases h0 : s'.objects[c.toObjId]? with
  | none => rw [h0] at e; cases e
  | some o =>
    rw [h0] at e
    cases o with
    | schedContext sc' =>
      simp only [schedBindingLinksOf, Option.some.injEq, Sum.inr.injEq] at e
      exact ⟨sc', (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr h0, e⟩
    | tcb _ => cases e
    | _ => cases e

end bindingLinksAgree

/-- A thread's home core is read off its affinity: states agreeing on every
affinity agree on every home core. -/
theorem schedAuxAgree.determineTargetCore_eq {st st' : SystemState} (h : schedAuxAgree st st')
    (tid : SeLe4n.ThreadId) : determineTargetCore st' tid = determineTargetCore st tid := by
  unfold determineTargetCore SystemState.getTcb?
  have e := h tid.toObjId
  cases hq : st'.objects[tid.toObjId]? with
  | none =>
    cases hp : st.objects[tid.toObjId]? with
    | none => rfl
    | some o => rw [hq, hp] at e; cases o <;> first | rfl | cases e
  | some o =>
    cases o with
    | tcb t =>
      rw [hq] at e
      obtain ⟨u, hu, -, hA⟩ := tcbSchedAuxOf_tcb e
      rw [hu]; simp only [hA]
    | _ =>
      cases hp : st.objects[tid.toObjId]? with
      | none => rfl
      | some o' => rw [hq, hp] at e; cases o' <;> first | rfl | cases e

-- ============================================================================
-- §3  The invariants transfer along the projections they read
-- ============================================================================

section transfer

variable {st st' : SystemState}

/-- No thread holds a budget after a step that keeps every thread's budget. -/
theorem allTimeoutBudgetsNone_of_aux (hA : schedAuxAgree st st')
    (h : allTimeoutBudgetsNone st) : allTimeoutBudgetsNone st' := by
  intro tid tcb hT
  have e := hA tid.toObjId; rw [hT] at e
  obtain ⟨u, hu, hb, -⟩ := tcbSchedAuxOf_tcb e
  rw [← hb]; exact h tid u hu

/-- The binding pair holds after a step that keeps every binding. -/
theorem schedContextBindingConsistent_of_binding (hB : bindingLinksAgree st st')
    (h : schedContextBindingConsistent st) : schedContextBindingConsistent st' := by
  refine ⟨fun tid tcb hT scId hb => ?_, fun scId sc hS tid hb => ?_⟩
  · obtain ⟨u, hu, e⟩ := hB.tcb_back hT
    obtain ⟨s, hs, hst⟩ := h.1 tid u hu scId (e.trans hb)
    obtain ⟨s', hs', e'⟩ := hB.symm.sc_back hs
    exact ⟨s', hs', e'.trans hst⟩
  · obtain ⟨u, hu, e⟩ := hB.sc_back hS
    obtain ⟨t, ht, hb'⟩ := h.2 scId u hu tid (e.trans hb)
    obtain ⟨t', ht', e'⟩ := hB.symm.tcb_back ht
    exact ⟨t', ht', e' ▸ hb'⟩

/-- Every queued context is bound after a step that keeps every binding and
every replenishment queue. -/
theorem replenishQueueEntriesBound_smp_of_frame (hB : bindingLinksAgree st st')
    (hR : ∀ c : CoreId, st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c)
    (h : replenishQueueEntriesBound_smp st) : replenishQueueEntriesBound_smp st' := by
  intro c scId t hMem
  rw [hR c] at hMem
  obtain ⟨sc, hS, tid, hb⟩ := h c scId t hMem
  obtain ⟨u, hu, e⟩ := hB.symm.getSchedContext?_back hS
  exact ⟨u, hu, tid, e.trans hb⟩

/-- Every queued context is queued on its thread's home core after a step that
keeps every binding, every affinity and every replenishment queue. -/
theorem replenishQueueAffinityConsistent_smp_of_frame (hB : bindingLinksAgree st st')
    (hA : schedAuxAgree st st')
    (hR : ∀ c : CoreId, st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c)
    (h : replenishQueueAffinityConsistent_smp st) : replenishQueueAffinityConsistent_smp st' := by
  intro c scId t hMem sc hS tid hb
  rw [hR c] at hMem
  obtain ⟨u, hu, e⟩ := hB.getSchedContext?_back hS
  rw [hA.determineTargetCore_eq]
  exact h c scId t hMem u hu tid (e.trans hb)

end transfer

namespace SchedLinkFrame

/-- **A frame step keeps every scheduling-link invariant.** -/
theorem preserves {st st' : SystemState} (h : SchedLinkFrame st st')
    (hI : schedContextLinkInvariant st) : schedContextLinkInvariant st' :=
  ⟨allTimeoutBudgetsNone_of_aux h.aux hI.budgets,
    schedContextBindingConsistent_of_binding h.binding hI.binding,
    replenishQueueEntriesBound_smp_of_frame h.binding h.replenish hI.replenishBound,
    replenishQueueAffinityConsistent_smp_of_frame h.binding h.aux h.replenish hI.replenishAffinity,
    h.releaseState.refined hI.refined⟩

end SchedLinkFrame

-- ============================================================================
-- §4  The frame's primitives
-- ============================================================================

/-- Two lookups that agree up to an object rewrite agree on any projection the
rewrite does not move. -/
theorem proj_eq_of_map_eq {α : Sort _} (f : Option KernelObject → α)
    (g : KernelObject → KernelObject) (hg : ∀ o, f (some (g o)) = f (some o))
    {a b : Option KernelObject} (h : a.map g = b.map g) : f a = f b := by
  cases a with
  | none => cases b with
    | none => rfl
    | some _ => cases h
  | some x => cases b with
    | none => cases h
    | some y =>
      simp only [Option.map_some, Option.some.injEq] at h
      rw [← hg x, h, hg y]

theorem tcbSchedAuxOf_withoutRunLinks (o : KernelObject) :
    tcbSchedAuxOf (some o.withoutRunLinks) = tcbSchedAuxOf (some o) := by
  cases o <;> rfl

theorem schedBindingLinksOf_withoutRunLinks (o : KernelObject) :
    schedBindingLinksOf (some o.withoutRunLinks) = schedBindingLinksOf (some o) := by
  cases o <;> rfl

theorem schedReleaseOf_withoutRunLinks (o : KernelObject) :
    schedReleaseOf (some o.withoutRunLinks) = schedReleaseOf (some o) := by
  cases o <;> rfl

theorem schedReleaseOf_withoutLinks (o : KernelObject) :
    schedReleaseOf (some o.withoutLinks) = schedReleaseOf (some o) := by
  cases o <;> rfl

theorem tcbSchedAuxOf_withoutLinks (o : KernelObject) :
    tcbSchedAuxOf (some o.withoutLinks) = tcbSchedAuxOf (some o) := by
  cases o <;> rfl

theorem schedBindingLinksOf_withoutLinks (o : KernelObject) :
    schedBindingLinksOf (some o.withoutLinks) = schedBindingLinksOf (some o) := by
  cases o <;> rfl

/-- An insert at a key whose projection it keeps keeps the projection at every
key. -/
theorem proj_insert_eq {α : Sort _} (f : Option KernelObject → α) {st : SystemState}
    {k : SeLe4n.ObjId} {o : KernelObject} (hInv : st.objects.invExt)
    (hk : f (some o) = f st.objects[k]?) (oid : SeLe4n.ObjId) :
    f (st.objects.insert k o)[oid]? = f st.objects[oid]? := by
  by_cases h : oid = k
  · subst h
    have e : (st.objects.insert oid o)[oid]? = some o :=
      RobinHood.RHTable.getElem?_insert_self st.objects oid o hInv
    rw [e]; exact hk
  · have e : (st.objects.insert k o)[oid]? = st.objects[oid]? :=
      RobinHood.RHTable.getElem?_insert_ne st.objects k oid o
        (by intro h'; exact h (eq_of_beq h').symm) hInv
    rw [e]

namespace SchedLinkFrame

/-- A step that writes no object and no release-queue slot. -/
theorem of_objects_eq {st st' : SystemState} (hO : st'.objects = st.objects)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots) :
    SchedLinkFrame st st' :=
  ⟨fun _ => by rw [hO], fun _ => by rw [hO], fun _ => by rw [hO], hS⟩

/-- A step that writes run-queue links alone, and no release-queue slot. -/
theorem of_agreeOffRunLinks {st st' : SystemState} (hA : st'.objectsAgreeOffRunLinks st)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots) :
    SchedLinkFrame st st' :=
  ⟨fun o => proj_eq_of_map_eq _ _ tcbSchedAuxOf_withoutRunLinks (hA o),
    fun o => proj_eq_of_map_eq _ _ schedBindingLinksOf_withoutRunLinks (hA o),
    fun o => proj_eq_of_map_eq _ _ schedReleaseOf_withoutRunLinks (hA o), hS⟩

/-- A step that writes derivation links alone, and no release-queue slot. -/
theorem of_agreeOffDerivationLinks {st st' : SystemState}
    (hA : SystemState.objectsAgreeOffDerivationLinks st' st)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots) :
    SchedLinkFrame st st' :=
  ⟨fun o => proj_eq_of_map_eq _ _ tcbSchedAuxOf_withoutLinks (hA o).map_withoutLinks,
    fun o => proj_eq_of_map_eq _ _ schedBindingLinksOf_withoutLinks (hA o).map_withoutLinks,
    fun o => proj_eq_of_map_eq _ _ schedReleaseOf_withoutLinks (hA o).map_withoutLinks, hS⟩

/-- An insert that keeps its key's projections, the scheduler untouched. -/
theorem of_insert {st : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hA : tcbSchedAuxOf (some o) = tcbSchedAuxOf st.objects[k]?)
    (hB : schedBindingLinksOf (some o) = schedBindingLinksOf st.objects[k]?)
    (hR : schedReleaseOf (some o) = schedReleaseOf st.objects[k]?) :
    SchedLinkFrame st { st with objects := st.objects.insert k o } :=
  ⟨proj_insert_eq _ hInv hA, proj_insert_eq _ hInv hB, proj_insert_eq _ hInv hR, rfl⟩

/-- A store that keeps its key's projections. -/
theorem storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hS : SeLe4n.Model.storeObject k o st = .ok ((), st'))
    (hA : tcbSchedAuxOf (some o) = tcbSchedAuxOf st.objects[k]?)
    (hB : schedBindingLinksOf (some o) = schedBindingLinksOf st.objects[k]?)
    (hR : schedReleaseOf (some o) = schedReleaseOf st.objects[k]?) :
    SchedLinkFrame st st' := by
  refine ⟨fun oid => ?_, fun oid => ?_, fun oid => ?_, by
    rw [storeObject_scheduler_eq st st' k o hS]⟩
  · by_cases h : oid = k
    · subst h; rw [storeObject_objects_eq st st' oid o hInv hS]; exact hA
    · rw [storeObject_objects_ne st st' k oid o h hInv hS]
  · by_cases h : oid = k
    · subst h; rw [storeObject_objects_eq st st' oid o hInv hS]; exact hB
    · rw [storeObject_objects_ne st st' k oid o h hInv hS]
  · by_cases h : oid = k
    · subst h; rw [storeObject_objects_eq st st' oid o hInv hS]; exact hR
    · rw [storeObject_objects_ne st st' k oid o h hInv hS]

/-- A stored object that keeps its key's projections. -/
theorem withObjectStored (st : SystemState) (k : SeLe4n.ObjId) (o : KernelObject)
    (hInv : st.objects.invExt) (hA : tcbSchedAuxOf (some o) = tcbSchedAuxOf st.objects[k]?)
    (hB : schedBindingLinksOf (some o) = schedBindingLinksOf st.objects[k]?)
    (hR : schedReleaseOf (some o) = schedReleaseOf st.objects[k]?) :
    SchedLinkFrame st (st.withObjectStored k o) :=
  storeObject hInv (SystemState.storeObject_eq_withObjectStored st k o) hA hB hR

/-- A thread rewritten in its slot keeping its binding codes, budget and
affinity. -/
theorem updateTcb (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt)
    (hf : ∀ x, (f x).scBindingScCode = x.scBindingScCode ∧
      (f x).scBindingOwnerCode = x.scBindingOwnerCode ∧ (f x).timeoutBudget = x.timeoutBudget ∧
      (f x).cpuAffinity = x.cpuAffinity := by intro _; exact ⟨rfl, rfl, rfl, rfl⟩) :
    SchedLinkFrame st (st.updateTcb t f) := by
  cases hG : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hG]; exact .refl st
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hG]
    have hPre := (SystemState.getTcb?_eq_some_iff st t x).mp hG
    obtain ⟨h1, h2, h3, h4⟩ := hf x
    exact of_insert hInv (by rw [hPre]; simp [tcbSchedAuxOf, h3, h4])
      (by rw [hPre]; simp [schedBindingLinksOf, h1, h2]) (by rw [hPre]; rfl)

/-- A scheduling context rewritten in its slot keeping its bound thread and
its release fields. -/
theorem updateSchedContext (st : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hInv : st.objects.invExt)
    (hf : ∀ x, (f x).boundThreadCode = x.boundThreadCode)
    (hr : ∀ x, (f x).releaseNextCode = x.releaseNextCode ∧ (f x).releaseCoreCode = x.releaseCoreCode ∧
      (f x).releaseAt = x.releaseAt := by intro _; exact ⟨rfl, rfl, rfl⟩) :
    SchedLinkFrame st (st.updateSchedContext scId f) := by
  cases hG : st.getSchedContext? scId with
  | none => rw [SystemState.updateSchedContext_eq_self_of_none hG]; exact .refl st
  | some x =>
    rw [SystemState.updateSchedContext_eq_of_some hG]
    have hPre := (SystemState.getSchedContext?_eq_some_iff st scId x).mp hG
    obtain ⟨r1, r2, r3⟩ := hr x
    exact of_insert hInv (by rw [hPre]; rfl) (by rw [hPre]; simp [schedBindingLinksOf, hf x])
      (by rw [hPre]; simp [schedReleaseOf, r1, r2, r3])

/-- An object rewritten in its slot by an update that keeps both projections of
every object. -/
theorem modifyObject (st : SystemState) (k : SeLe4n.ObjId) (f : KernelObject → KernelObject)
    (hInv : st.objects.invExt)
    (hf : ∀ o, tcbSchedAuxOf (some (f o)) = tcbSchedAuxOf (some o) ∧
      schedBindingLinksOf (some (f o)) = schedBindingLinksOf (some o) ∧
      schedReleaseOf (some (f o)) = schedReleaseOf (some o)) :
    SchedLinkFrame st (st.modifyObject k f) := by
  unfold SystemState.modifyObject
  cases hG : st.objects[k]? with
  | none =>
    have e : st.objects.modify k f = st.objects := by
      unfold RobinHood.RHTable.modify; rw [← RHTable_getElem?_eq_get?, hG]
    exact of_objects_eq (by rw [e]) rfl
  | some o =>
    rw [RobinHood.RHTable.modify_of_get? hG]
    exact of_insert hInv (by rw [hG]; exact (hf o).1) (by rw [hG]; exact (hf o).2.1)
      (by rw [hG]; exact (hf o).2.2)

end SchedLinkFrame

-- ============================================================================
-- §5  The finalisation's steps that write none of it
-- ============================================================================

namespace SchedLinkFrame

/-- A step that writes run-queue links and the scheduler's other fields alone. -/
theorem descheduleAt (st : SystemState) (t : SeLe4n.ThreadId) (p : Option CoreId) :
    SchedLinkFrame st (SeLe4n.Kernel.descheduleAt st t p) := by
  cases p with
  | none => exact .refl st
  | some c =>
    exact of_agreeOffRunLinks (removeRunnableOnCore_objectsAgreeOffRunLinks st t c)
      (removeRunnableOnCore_releaseSlots st t c)

theorem descheduleAtPlacement (st : SystemState) (t : SeLe4n.ThreadId) :
    SchedLinkFrame st (SeLe4n.Kernel.descheduleAtPlacement st t) :=
  of_agreeOffRunLinks (descheduleAtPlacement_objectsAgreeOffRunLinks st t)
    (descheduleAtPlacement_releaseSlots st t)

theorem markKeyChangeFrom (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    SchedLinkFrame st (SeLe4n.Kernel.markKeyChangeFrom pre st tid) :=
  of_objects_eq (markKeyChangeFrom_objects pre st tid) (markKeyChangeFrom_releaseSlots pre st tid)

theorem releaseCores (st : SystemState) (t : SeLe4n.ThreadId) :
    SchedLinkFrame st (finaliseThreadReleaseCores st t) :=
  of_objects_eq (finaliseThreadReleaseCores_objects st t)
    (by rw [finaliseThreadReleaseCores_scheduler])

/-- The wake: a run-queue insert and the `.ready` mark. -/
theorem enqueueRunnableOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : SchedLinkFrame st (SeLe4n.Kernel.enqueueRunnableOnCore st c t) := by
  cases hT : st.getTcb? t with
  | none =>
    simp only [SeLe4n.Kernel.enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_none hT]
    exact .refl st
  | some tcb =>
    cases hD : wakeDeclines st c t with
    | true =>
      simp only [SeLe4n.Kernel.enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_some hT, hD,
        if_true]
      exact .refl st
    | false =>
      have hPre := (SystemState.getTcb?_eq_some_iff st t tcb).mp hT
      have h1 := of_insert (st := st) (k := t.toObjId) (o := .tcb (tcb.setIpcState .ready)) hInv
        (by rw [hPre]; rfl) (by rw [hPre]; rfl) (by rw [hPre]; rfl)
      exact h1.trans (of_agreeOffRunLinks (enqueueRunnableOnCore_objectsAgree_marked st c t tcb hT hD)
        (enqueueRunnableOnCore_releaseSlots st c t))

theorem suspend (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    SchedLinkFrame st ((SeLe4n.Kernel.descheduleAtPlacement st t).updateTcb t finalisedSuspendMark) :=
  (descheduleAtPlacement st t).trans
    (updateTcb _ t _ (FinaliseFrame.descheduleAt st t _ hInv).invExt)

/-- A finalised thread's suspend, its guard read or not. -/
theorem finaliseThreadSuspend (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    SchedLinkFrame st (SeLe4n.Kernel.finaliseThreadSuspend st t) := by
  unfold SeLe4n.Kernel.finaliseThreadSuspend
  split
  · split
    · exact suspend st t hInv
    · exact .refl st
  · exact .refl st

end SchedLinkFrame

/-- An object rewritten in its slot keeps the object table well formed. -/
theorem modifyObject_preserves_objects_invExt {st : SystemState} {k : SeLe4n.ObjId}
    {f : KernelObject → KernelObject} (hInv : st.objects.invExt) :
    (st.modifyObject k f).objects.invExt := by
  unfold SystemState.modifyObject
  cases hG : st.objects[k]? with
  | none =>
    have e : st.objects.modify k f = st.objects := by
      unfold RobinHood.RHTable.modify; rw [← RHTable_getElem?_eq_get?, hG]
    show (st.objects.modify k f).invExt
    rw [e]; exact hInv
  | some o =>
    show (st.objects.modify k f).invExt
    rw [RobinHood.RHTable.modify_of_get? hG]
    exact RHTable_insert_preserves_invExt _ _ _ hInv

namespace SchedLinkFrame

/-- An object rewritten by an update that turns a thread or a context into
none, and keeps every other object's kind out of both. -/
theorem modifyObject_inert (st : SystemState) (k : SeLe4n.ObjId) (f : KernelObject → KernelObject)
    (hInv : st.objects.invExt) (hT : ∀ t, f (.tcb t) = .tcb t)
    (hS : ∀ sc, f (.schedContext sc) = .schedContext sc)
    (hO : ∀ o, (∀ t, o ≠ .tcb t) → (∀ sc, o ≠ .schedContext sc) →
      (∀ t, f o ≠ .tcb t) ∧ (∀ sc, f o ≠ .schedContext sc)) :
    SchedLinkFrame st (st.modifyObject k f) := by
  refine modifyObject st k f hInv (fun o => ?_)
  by_cases h1 : ∃ t, o = .tcb t
  · obtain ⟨t, rfl⟩ := h1; rw [hT]; exact ⟨rfl, rfl, rfl⟩
  by_cases h2 : ∃ sc, o = .schedContext sc
  · obtain ⟨sc, rfl⟩ := h2; rw [hS]; exact ⟨rfl, rfl, rfl⟩
  have n1 : ∀ t, o ≠ .tcb t := fun t e => h1 ⟨t, e⟩
  have n2 : ∀ sc, o ≠ .schedContext sc := fun sc e => h2 ⟨sc, e⟩
  obtain ⟨m1, m2⟩ := hO o n1 n2
  have a : ∀ x : KernelObject, (∀ t, x ≠ .tcb t) → (∀ sc, x ≠ .schedContext sc) →
      tcbSchedAuxOf (some x) = none ∧ schedBindingLinksOf (some x) = none ∧
        schedReleaseOf (some x) = none := by
    intro x h h'
    cases x with
    | tcb t => exact absurd rfl (h t)
    | schedContext sc => exact absurd rfl (h' sc)
    | _ => exact ⟨rfl, rfl, rfl⟩
  rw [(a _ m1 m2).1, (a _ m1 m2).2.1, (a _ m1 m2).2.2, (a _ n1 n2).1, (a _ n1 n2).2.1,
    (a _ n1 n2).2.2]
  exact ⟨rfl, rfl, rfl⟩

/-- An endpoint update: endpoints to endpoints, every other object kept. -/
theorem modifyObject_endpoint (st : SystemState) (k : SeLe4n.ObjId) (f : KernelObject → KernelObject)
    (hInv : st.objects.invExt) (hE : ∀ e, ∃ e', f (.endpoint e) = .endpoint e')
    (hO : ∀ o, (∀ e, o ≠ .endpoint e) → f o = o) :
    SchedLinkFrame st (st.modifyObject k f) :=
  modifyObject_inert st k f hInv (fun t => hO _ (fun _ e => by cases e))
    (fun sc => hO _ (fun _ e => by cases e)) (fun o n1 n2 => by
      by_cases h : ∃ e, o = .endpoint e
      · obtain ⟨e, rfl⟩ := h; obtain ⟨e', h'⟩ := hE e; rw [h']
        exact ⟨fun _ e => KernelObject.noConfusion e, fun _ e => KernelObject.noConfusion e⟩
      · rw [hO o (fun e he => h ⟨e, he⟩)]; exact ⟨n1, n2⟩)

/-- A notification update: notifications to notifications, every other object
kept. -/
theorem modifyObject_notification (st : SystemState) (k : SeLe4n.ObjId)
    (f : KernelObject → KernelObject) (hInv : st.objects.invExt)
    (hN : ∀ n, ∃ n', f (.notification n) = .notification n')
    (hO : ∀ o, (∀ n, o ≠ .notification n) → f o = o) :
    SchedLinkFrame st (st.modifyObject k f) :=
  modifyObject_inert st k f hInv (fun t => hO _ (fun _ e => by cases e))
    (fun sc => hO _ (fun _ e => by cases e)) (fun o n1 n2 => by
      by_cases h : ∃ n, o = .notification n
      · obtain ⟨n, rfl⟩ := h; obtain ⟨n', h'⟩ := hN n; rw [h']
        exact ⟨fun _ e => KernelObject.noConfusion e, fun _ e => KernelObject.noConfusion e⟩
      · rw [hO o (fun n hn => h ⟨n, hn⟩)]; exact ⟨n1, n2⟩)

/-- The pop of an endpoint queue's head. -/
theorem storePopHead (st : SystemState) (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    SchedLinkFrame st (SeLe4n.Kernel.storePopHead st endpointId isReceiveQ head next) := by
  have h1 := modifyObject_endpoint st endpointId (popEndpoint isReceiveQ (SeLe4n.ThreadId.optCode next))
    hInv (fun e => by simp only [popEndpoint]; split <;> exact ⟨_, rfl⟩)
    (fun o h => by cases o <;> first | rfl | exact absurd rfl (h _))
  have i1 := (FinaliseFrame.storePopHead st endpointId isReceiveQ head next hInv)
  cases next with
  | none =>
    simp only [SeLe4n.Kernel.storePopHead]
    exact h1.trans (updateTcb _ _ _
      (FinaliseFrame.modifyObject st endpointId _ hInv (fun o => by
        cases o with
        | endpoint e =>
          right; simp only [popEndpoint]
          split <;> exact ⟨rfl, rfl, rfl, Or.inr (Or.inl rfl), by simp [KernelObject.objectType]⟩
        | _ => exact Or.inl rfl)).invExt)
  | some n =>
    simp only [SeLe4n.Kernel.storePopHead]
    have j1 := FinaliseFrame.modifyObject st endpointId
      (popEndpoint isReceiveQ (SeLe4n.ThreadId.optCode (some n))) hInv (fun o => by
        cases o with
        | endpoint e =>
          right; simp only [popEndpoint]
          split <;> exact ⟨rfl, rfl, rfl, Or.inr (Or.inl rfl), by simp [KernelObject.objectType]⟩
        | _ => exact Or.inl rfl)
    have j2 := j1.trans (FinaliseFrame.updateTcb _ n tcbAsQueueHead j1.invExt)
    exact (h1.trans (updateTcb _ n tcbAsQueueHead j1.invExt)).trans (updateTcb _ _ _ j2.invExt)

end SchedLinkFrame

namespace SchedLinkFrame

theorem wakeCancelledWaiter (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    SchedLinkFrame st (SeLe4n.Kernel.wakeCancelledWaiter st t) :=
  enqueueRunnableOnCore st _ t hInv

/-- An endpoint waiter's cancel: the pop, the thread's IPC ended, the wake. -/
theorem storeEndpointWaiterCancelled (st : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (t : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    SchedLinkFrame st (SeLe4n.Kernel.storeEndpointWaiterCancelled st endpointId isReceiveQ t next) := by
  unfold SeLe4n.Kernel.storeEndpointWaiterCancelled
  have i1 := FinaliseFrame.storePopHead st endpointId isReceiveQ t next hInv
  have i2 := i1.trans (FinaliseFrame.updateTcb _ t cancelledEndpointWaiterTcb i1.invExt)
  exact ((storePopHead st endpointId isReceiveQ t next hInv).trans
    (updateTcb _ t cancelledEndpointWaiterTcb i1.invExt)).trans (wakeCancelledWaiter _ t i2.invExt)

/-- The removal of a waiter from anywhere in an endpoint queue. -/
theorem storeQueueRemove (st : SystemState) (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB) (hInv : st.objects.invExt) :
    SchedLinkFrame st (SeLe4n.Kernel.storeQueueRemove st endpointId isReceiveQ tid ep tcb) := by
  have hHead : ∀ (s : SystemState) (c : Nat), s.objects.invExt →
      SchedLinkFrame s (s.modifyObject endpointId (headAdvancedEndpoint isReceiveQ c)) :=
    fun s c hI => modifyObject_endpoint s endpointId _ hI
      (fun e => by simp only [headAdvancedEndpoint]; exact ⟨_, rfl⟩)
      (fun o h => by cases o <;> first | rfl | exact absurd rfl (h _))
  have hEnds : ∀ (s : SystemState) (h t : Nat), s.objects.invExt →
      SchedLinkFrame s (s.modifyObject endpointId (endsSetEndpoint isReceiveQ h t)) :=
    fun s h t hI => modifyObject_endpoint s endpointId _ hI
      (fun e => by simp only [endsSetEndpoint]; exact ⟨_, rfl⟩)
      (fun o h => by cases o <;> first | rfl | exact absurd rfl (h _))
  have h1 : (match tcb.queuePPrev with
      | some .endpointHead =>
        st.modifyObject endpointId (headAdvancedEndpoint isReceiveQ tcb.queueNextCode)
      | some (.tcbNext p) => st.updateTcb p (queueUnlinkPredecessor tcb)
      | none => st).objects.invExt ∧ SchedLinkFrame st (match tcb.queuePPrev with
      | some .endpointHead =>
        st.modifyObject endpointId (headAdvancedEndpoint isReceiveQ tcb.queueNextCode)
      | some (.tcbNext p) => st.updateTcb p (queueUnlinkPredecessor tcb)
      | none => st) := by
    split
    · exact ⟨modifyObject_preserves_objects_invExt hInv, hHead st _ hInv⟩
    · exact ⟨SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv, updateTcb st _ _ hInv⟩
    · exact ⟨hInv, .refl st⟩
  have hFin : ∀ (s2 : SystemState) (h t : Nat), s2.objects.invExt → SchedLinkFrame st s2 →
      SchedLinkFrame st ((s2.modifyObject endpointId (endsSetEndpoint isReceiveQ h t)).updateTcb
        tid tcbOffQueue) := fun s2 h t i2 h2 =>
    (h2.trans (hEnds s2 h t i2)).trans
      (updateTcb _ tid tcbOffQueue (modifyObject_preserves_objects_invExt i2))
  have hNext : ∀ (s1 : SystemState), s1.objects.invExt ∧ SchedLinkFrame st s1 →
      (match tcb.queueNext with
        | some n => s1.updateTcb n (queueUnlinkSuccessor tcb)
        | none => s1).objects.invExt ∧ SchedLinkFrame st (match tcb.queueNext with
        | some n => s1.updateTcb n (queueUnlinkSuccessor tcb)
        | none => s1) := by
    intro s1 h1
    split
    · exact ⟨SystemState.updateTcb_preserves_objects_invExt _ _ _ h1.1,
        h1.2.trans (updateTcb s1 _ _ h1.1)⟩
    · exact h1
  unfold SeLe4n.Kernel.storeQueueRemove
  have r := hNext _ h1
  exact hFin _ _ _ r.1 r.2

end SchedLinkFrame

namespace SchedLinkFrame

/-- A thread's endpoint cancel: the removal, then its IPC ended. -/
theorem storeEndpointBlockedCancelled (st : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB)
    (hInv : st.objects.invExt) :
    SchedLinkFrame st
      (SeLe4n.Kernel.storeEndpointBlockedCancelled st endpointId isReceiveQ tid ep tcb) := by
  unfold SeLe4n.Kernel.storeEndpointBlockedCancelled
  exact (storeQueueRemove st endpointId isReceiveQ tid ep tcb hInv).trans
    (updateTcb _ tid cancelledEndpointWaiterTcb
      (FinaliseFrame.storeQueueRemove st endpointId isReceiveQ tid ep tcb hInv).invExt)

/-- The unlink of a thread from its notification's queue writes notifications
and the threads' notification links alone. -/
theorem of_ntfnUnlinkReach {st s : SystemState} (h : ntfnUnlinkReach st s)
    (hS : s.scheduler.releaseSlots = st.scheduler.releaseSlots) :
    SchedLinkFrame st s := by
  have hP : ∀ (oid : SeLe4n.ObjId), tcbSchedAuxOf s.objects[oid]? = tcbSchedAuxOf st.objects[oid]? ∧
      schedBindingLinksOf s.objects[oid]? = schedBindingLinksOf st.objects[oid]? ∧
      schedReleaseOf s.objects[oid]? = schedReleaseOf st.objects[oid]? := by
    intro oid
    rcases h.2 oid with e | ⟨n, n', h0, h1, -⟩ | ⟨t, t', h0, h1, np, nn, e⟩
    · rw [e]; exact ⟨rfl, rfl, rfl⟩
    · rw [h0, h1]; exact ⟨rfl, rfl, rfl⟩
    · rw [h0, h1, e]; exact ⟨rfl, rfl, rfl⟩
  exact ⟨fun oid => (hP oid).1, fun oid => (hP oid).2.1, fun oid => (hP oid).2.2, hS⟩

/-- A notification waiter's cancel: it leaves the notification's queue and is
restored. -/
theorem notificationCancel (st : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB)
    (n : SeLe4n.ObjId) (hInv : st.objects.invExt)
    (hB : tcb.ipcState = .blockedOnNotification n) :
    SchedLinkFrame st (Lifecycle.Suspend.cancelIpcBlocking st t tcb) := by
  have hEq : Lifecycle.Suspend.cancelIpcBlocking st t tcb =
      Lifecycle.Suspend.restoreToReadyCancelled (removeFromNotificationWaitQueue st t) t := by
    unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
  rw [hEq]
  have hR := removeFromNotificationWaitQueue_reach st t hInv
  obtain ⟨objs, e⟩ := removeFromNotificationWaitQueue_eq_objects st t
  have h1 : SchedLinkFrame st (removeFromNotificationWaitQueue st t) :=
    of_ntfnUnlinkReach hR (by rw [e])
  unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
  exact h1.trans (updateTcb _ _ _ hR.1)

/-- The unbind, each side in its slot. -/
theorem storeUnbindNotification (st : SystemState) (t : SeLe4n.ThreadId) (n : SeLe4n.ObjId)
    (hInv : st.objects.invExt) :
    SchedLinkFrame st (SeLe4n.Kernel.storeUnbindNotification st t n) := by
  unfold SeLe4n.Kernel.storeUnbindNotification
  exact (updateTcb st t (fun x => { x with boundNotificationCode := 0 }) hInv).trans
    (modifyObject_notification _ n _ (SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv)
      (fun m => ⟨_, rfl⟩) (fun o h => by cases o <;> first | rfl | exact absurd rfl (h _)))

/-- The unstack: the head reply's upward link cleared, then the context's head. -/
theorem unstack {s s1 : SystemState} {x : SeLe4n.ObjId} {rid : SeLe4n.ReplyId} {r : Reply}
    (hInv : s.objects.invExt) (hR : s.getReply? rid = some r)
    (hS : SeLe4n.Model.storeObject rid.toObjId (.reply { r with next := none }) s = .ok ((), s1)) :
    SchedLinkFrame s (s1.updateSchedContext ⟨x.val⟩ fun sc => { sc with scReply := none }) := by
  have hPre := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
  exact (storeObject hInv hS (by rw [hPre]; rfl) (by rw [hPre]; rfl) (by rw [hPre]; rfl)).trans
    (updateSchedContext _ _ _ (storeObject_preserves_objects_invExt s s1 _ _ hInv hS) (fun _ => rfl))

/-- **The priority-inheritance walk**: boosts and run-queue moves, threads
rewritten keeping every field the invariants read. -/
theorem propagatePip (st : SystemState) (s : SeLe4n.ThreadId) (ec : CoreId)
    (fuel : Nat) (hInv : st.objects.invExt) :
    SchedLinkFrame st (PriorityInheritance.propagatePipChainCrossCore st s ec fuel).1 := by
  have hP : ∀ oid : SeLe4n.ObjId,
      tcbSchedAuxOf (PriorityInheritance.propagatePipChainCrossCore st s ec fuel).1.objects[oid]? =
        tcbSchedAuxOf st.objects[oid]? ∧
      schedBindingLinksOf (PriorityInheritance.propagatePipChainCrossCore st s ec fuel).1.objects[oid]? =
        schedBindingLinksOf st.objects[oid]? ∧
      schedReleaseOf (PriorityInheritance.propagatePipChainCrossCore st s ec fuel).1.objects[oid]? =
        schedReleaseOf st.objects[oid]? := by
    intro oid
    rcases PriorityInheritance.propagatePipChainCrossCore_objects_pointwise fuel st s ec hInv oid with
      e | ⟨pre, post, hp, hq, -⟩
    · rw [e]; exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨ty, p, hy, hE⟩ := PriorityInheritance.propagatePipChainCrossCore_tcb_backward st s ec
        fuel hInv ⟨oid.val⟩ post hq
      rw [show (⟨oid.val⟩ : SeLe4n.ThreadId).toObjId = oid from rfl, hp] at hy
      cases hy
      rw [hp, hq]
      have p1 := TCB.proj_eq_of_withoutRunLinks_eq (·.timeoutBudget) hE
      have p2 := TCB.proj_eq_of_withoutRunLinks_eq (·.cpuAffinity) hE
      have p3 := TCB.proj_eq_of_withoutRunLinks_eq (·.scBindingScCode) hE
      have p4 := TCB.proj_eq_of_withoutRunLinks_eq (·.scBindingOwnerCode) hE
      simp only at p1 p2 p3 p4
      simp only [tcbSchedAuxOf, schedBindingLinksOf, schedReleaseOf, p1, p2, p3, p4, and_self]
  exact ⟨fun oid => (hP oid).1, fun oid => (hP oid).2.1, fun oid => (hP oid).2.2,
    PriorityInheritance.propagatePipChainCrossCore_releaseSlots st s ec fuel⟩

/-- The revert of a finalised reply's caller's boost. -/
theorem finaliseReplyRevert (st : SystemState) (server? : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : SchedLinkFrame st (SeLe4n.Kernel.finaliseReplyRevert st server?) := by
  cases server? with
  | none => exact .refl st
  | some s => exact propagatePip st s _ _ hInv

end SchedLinkFrame

-- ============================================================================
-- §6  A context's release of its holder
-- ============================================================================

namespace schedAuxAgree

theorem trans {a b c : SystemState} (h₁ : schedAuxAgree a b) (h₂ : schedAuxAgree b c) :
    schedAuxAgree a c := fun o => (h₂ o).trans (h₁ o)

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) : schedAuxAgree st st' :=
  fun _ => by rw [h]

/-- A step writing contexts' release fields alone keeps every budget and affinity. -/
theorem of_objectsAgreeOffReleaseLinks {st st' : SystemState}
    (h : st'.objectsAgreeOffReleaseLinks st) : schedAuxAgree st st' :=
  fun o => proj_eq_of_map_eq _ _ (fun x => by cases x <;> rfl) (h o)

/-- A thread rewritten in its slot keeping its budget and affinity. -/
theorem updateTcb (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt)
    (hf : ∀ x, (f x).timeoutBudget = x.timeoutBudget ∧ (f x).cpuAffinity = x.cpuAffinity) :
    schedAuxAgree st (st.updateTcb t f) := by
  cases hG : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hG]; exact fun _ => rfl
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hG]
    have hPre := (SystemState.getTcb?_eq_some_iff st t x).mp hG
    exact proj_insert_eq _ hInv (by rw [hPre]; simp [tcbSchedAuxOf, (hf x).1, (hf x).2])

/-- A scheduling context rewritten in its slot. -/
theorem updateSchedContext (st : SystemState) (s : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hInv : st.objects.invExt) :
    schedAuxAgree st (st.updateSchedContext s f) := by
  cases hG : st.getSchedContext? s with
  | none => rw [SystemState.updateSchedContext_eq_self_of_none hG]; exact fun _ => rfl
  | some x =>
    rw [SystemState.updateSchedContext_eq_of_some hG]
    have hPre := (SystemState.getSchedContext?_eq_some_iff st s x).mp hG
    exact proj_insert_eq _ hInv (by rw [hPre]; rfl)

end schedAuxAgree

/-- **The release keeps every scheduling-link invariant**: the context's
bound-thread code and the thread's binding codes are cleared together, so no
other thread or context loses its partner; the context's replenishments are
purged on its holder's home core, which is the only core that queues them
(`replenishQueueAffinityConsistent_smp`), so no core keeps a replenishment for
an unbound context. -/
theorem finaliseScRelease_preserves_schedContextLinkInvariant {s s' : SystemState}
    {t : SeLe4n.ThreadId} {tcb : TCB} {sc : SchedContext} {x : SeLe4n.ObjId}
    (hInv : s.objects.invExt) (hI : schedContextLinkInvariant s)
    (hT : s.getTcb? t = some tcb) (hS : tcb.scBindingScCode = x.val + 1)
    (hSc : s.getSchedContext? ⟨x.val⟩ = some sc) (hB : sc.boundThreadCode = t.val + 1)
    (hOk : cancelBoundDonationOnCore s t { tcb with scBindingOwnerCode := 0 }
      = .ok s') : schedContextLinkInvariant s' := by
  have hBind : ({ tcb with scBindingOwnerCode := 0 } : TCB).schedContextBinding =
      .bound ⟨x.val⟩ := by
    unfold TCB.schedContextBinding; simp only [hS]; rfl
  generalize hId : (⟨x.val⟩ : SeLe4n.SchedContextId) = scId at hBind hSc
  obtain ⟨hTSelf, hTNe⟩ := cancelBoundDonationOnCore_getTcb? s s' t _ scId hBind hInv hOk
  obtain ⟨hSSelf, hSNe⟩ := cancelBoundDonationOnCore_getSchedContext? s s' t _ scId hBind hInv hOk
  have hObjs := cancelBoundDonationOnCore_objects s s' t _ scId hBind hInv hOk
  have hBt : sc.boundThread = some t := by
    simp only [SchedContext.boundThread, hB]; rfl
  have hScId : (TCB.schedContextBinding tcb).scId? = some scId := by
    subst hId; unfold TCB.schedContextBinding; rw [hS]
    cases tcb.scBindingOwnerCode <;> rfl
  -- The budgets and affinities: two slot rewrites keeping them.
  have hAux : schedAuxAgree s s' := by
    have h1 := schedAuxAgree.updateSchedContext s scId
      (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) hInv
    have h2 := schedAuxAgree.updateTcb (s.updateSchedContext scId
      (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })) t
      (fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 })
      (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv) (fun _ => ⟨rfl, rfl⟩)
    exact (h1.trans h2).trans (schedAuxAgree.of_objectsAgreeOffReleaseLinks hObjs)
  have hTPost : s'.getTcb? t = some { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 } := by
    rw [hTSelf, hT]; rfl
  have hTNe' : ∀ u : SeLe4n.ThreadId, u ≠ t → s'.getTcb? u = s.getTcb? u := fun u hu =>
    hTNe u (fun e => hu (SeLe4n.ThreadId.toObjId_injective _ _ e))
  have hSNe' : ∀ s0 : SeLe4n.SchedContextId, s0 ≠ scId →
      (s'.getSchedContext? s0).map SchedContext.withoutRelease =
        (s.getSchedContext? s0).map SchedContext.withoutRelease := fun s0 hs =>
    hSNe s0 (fun e => hs (SeLe4n.SchedContextId.toObjId_injective _ _ e))
  have hSFwd : ∀ s0 : SeLe4n.SchedContextId, s0 ≠ scId → ∀ sc1, s.getSchedContext? s0 = some sc1 →
      ∃ sc1', s'.getSchedContext? s0 = some sc1' ∧ sc1'.boundThread = sc1.boundThread :=
    fun s0 hs sc1 h1 =>
      let ⟨sc1', h, hw⟩ := SchedContext.map_withoutRelease_some (hSNe' s0 hs) h1
      ⟨sc1', h, SchedContext.proj_eq_of_withoutRelease_eq (·.boundThread) hw⟩
  have hSBack : ∀ s0 : SeLe4n.SchedContextId, s0 ≠ scId → ∀ sc0, s'.getSchedContext? s0 = some sc0 →
      ∃ sc0', s.getSchedContext? s0 = some sc0' ∧ sc0'.boundThread = sc0.boundThread :=
    fun s0 hs sc0 h0 =>
      let ⟨sc0', h, hw⟩ := SchedContext.map_withoutRelease_some (hSNe' s0 hs).symm h0
      ⟨sc0', h, SchedContext.proj_eq_of_withoutRelease_eq (·.boundThread) hw⟩
  have hSPost : ∀ sc', s'.getSchedContext? scId = some sc' → sc'.boundThread = none := by
    intro sc' h; rw [h, hSc] at hSSelf; exact Option.some.inj hSSelf
  have tcbIff := fun (u : SeLe4n.ThreadId) (st : SystemState) (v : TCB) =>
    (SystemState.getTcb?_eq_some_iff st u v)
  have scIff := fun (u : SeLe4n.SchedContextId) (st : SystemState) (v : SchedContext) =>
    (SystemState.getSchedContext?_eq_some_iff st u v)
  -- The binding pair.
  have hCons : schedContextBindingConsistent s' := by
    refine ⟨fun u tu hU s0 hb => ?_, fun s0 sc0 hS0 y hy => ?_⟩
    · have hU' := (tcbIff u s' tu).mpr hU
      by_cases hu : u = t
      · subst hu; rw [hTPost] at hU'; cases hU'
        exact absurd hb (by simp [TCB.schedContextBinding, SchedContextBinding.ofCodes])
      · rw [hTNe' u hu] at hU'
        obtain ⟨sc1, hsc1, hbt1⟩ := hI.binding.1 u tu ((tcbIff u s tu).mp hU') s0 hb
        by_cases hs : s0 = scId
        · subst hs
          rw [(scIff _ s sc).mp hSc] at hsc1; cases hsc1
          rw [hBt] at hbt1; exact absurd (Option.some.inj hbt1).symm hu
        · obtain ⟨sc1', h1', hbt⟩ := hSFwd s0 hs sc1 ((scIff s0 s sc1).mpr hsc1)
          exact ⟨sc1', (scIff s0 s' sc1').mp h1', hbt.trans hbt1⟩
    · have hS0' := (scIff s0 s' sc0).mpr hS0
      by_cases hs : s0 = scId
      · subst hs; rw [hSPost sc0 hS0'] at hy; cases hy
      · obtain ⟨sc0', hS0'', hbt⟩ := hSBack s0 hs sc0 hS0'
        obtain ⟨ty, hty, hbb⟩ := hI.binding.2 s0 sc0' ((scIff s0 s sc0').mp hS0'') y
          (hbt.trans hy)
        by_cases hyt : y = t
        · subst hyt
          rw [(tcbIff y s tcb).mp hT] at hty; cases hty
          exfalso; apply hs
          have : (TCB.schedContextBinding tcb).scId? = some s0 := by
            rcases hbb with h | ⟨_, h⟩ <;> rw [h] <;> rfl
          rw [hScId] at this; exact (Option.some.inj this).symm
        · refine ⟨ty, (tcbIff y s' ty).mp ?_, hbb⟩
          rw [hTNe' y hyt]; exact (tcbIff y s ty).mpr hty
  -- The replenishment pair: the purge leaves no entry naming the context.
  have hBound : replenishQueueEntriesBound_smp s' := by
    intro c s0 n hMem
    obtain ⟨hm, hs⟩ := cancelBoundDonationOnCore_replenishQueue_purged_of_refined s s' t _ scId
      hBind hInv hI.refined hOk c (s0, n) hMem
    obtain ⟨sc1, h1, tid, hb⟩ := hI.replenishBound c s0 n hm
    obtain ⟨sc1', h1', hbt⟩ := hSFwd s0 hs sc1 h1
    exact ⟨sc1', h1', tid, hbt.trans hb⟩
  exact ⟨allTimeoutBudgetsNone_of_aux hAux hI.budgets, hCons, hBound,
    cancelBoundDonationOnCore_preserves_replenishQueueAffinityConsistent_smp s s' t _ hInv
      hI.replenishAffinity hOk, cancelBoundDonationOnCore_refined hInv hI.refined hOk⟩

-- ============================================================================
-- §7  A reply's caller cancel, its loan handed back
-- ============================================================================

/-- **The donation pop keeps the budgets, the binding pair and the bound
replenishments**: it moves one reciprocal pair from its holder to its recipient
(`returnDonatedSchedContext_preserves_schedContextBindingConsistent`), writes no
budget, and leaves the context bound and every replenishment queue as it was. -/
theorem returnDonatedSchedContext_preserves_schedLinks {st st' : SystemState}
    {serverTid : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId}
    {originalOwner : SeLe4n.ThreadId} {newOwner? : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (hB : allTimeoutBudgetsNone st)
    (hC : schedContextBindingConsistent st) (hR : replenishQueueEntriesBound_smp st)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    allTimeoutBudgetsNone st' ∧ schedContextBindingConsistent st' ∧
      replenishQueueEntriesBound_smp st' := by
  refine ⟨fun tid tcb hT => ?_, returnDonatedSchedContext_preserves_schedContextBindingConsistent
    st st' serverTid scId originalOwner newOwner? hInv hC h, fun c s0 n hMem => ?_⟩
  · obtain ⟨tcb0, h0, e⟩ := returnDonatedSchedContext_tcb_timeoutBudget_backward st st' serverTid
      scId originalOwner hInv newOwner? h tid.toObjId tcb hT
    rw [← e]; exact hB tid tcb0 h0
  · have hSch := returnDonatedSchedContext_scheduler_eq st st' serverTid scId originalOwner newOwner? h
    have hQ : st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
      rw [hSch]; rfl
    rw [hQ] at hMem
    by_cases hs : s0 = scId
    · subst hs
      obtain ⟨sc', h1, h2⟩ := returnDonatedSchedContext_post_boundThread st st' serverTid s0
        originalOwner hInv newOwner? h
      exact ⟨sc', h1, originalOwner, h2⟩
    · obtain ⟨sc1, h1, tid, hb⟩ := hR c s0 n hMem
      exact ⟨sc1, by rw [returnDonatedSchedContext_getSchedContext?_ne st st' serverTid scId s0
        originalOwner hs hInv newOwner? h]; exact h1, tid, hb⟩

/-- ...and so does a cancelled caller's donation return, or its refusal. -/
theorem returnDonationToCancelledCaller_preserves_schedLinks (st : SystemState)
    (c : SeLe4n.ThreadId) (t : TCB) (hInv : st.objects.invExt) (hB : allTimeoutBudgetsNone st)
    (hC : schedContextBindingConsistent st) (hR : replenishQueueEntriesBound_smp st) :
    allTimeoutBudgetsNone (Lifecycle.Suspend.returnDonationToCancelledCaller st c t) ∧
      schedContextBindingConsistent (Lifecycle.Suspend.returnDonationToCancelledCaller st c t) ∧
      replenishQueueEntriesBound_smp (Lifecycle.Suspend.returnDonationToCancelledCaller st c t) := by
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  split
  · split
    · rename_i hOk
      obtain ⟨n, -, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hOk
      exact returnDonatedSchedContext_preserves_schedLinks hInv hB hC hR hPop
    · exact ⟨hB, hC, hR⟩
  · exact ⟨hB, hC, hR⟩

namespace SchedLinkFrame

/-- A reply stored over a reply. -/
theorem storeReplyOver {st st' : SystemState} {k : SeLe4n.ObjId} {o o' : Reply}
    (hInv : st.objects.invExt) (hPre : st.objects[k]? = some (.reply o))
    (hS : SeLe4n.Model.storeObject k (.reply o') st = .ok ((), st')) : SchedLinkFrame st st' :=
  storeObject hInv hS (by rw [hPre]; rfl) (by rw [hPre]; rfl) (by rw [hPre]; rfl)

/-- The splice of a reply off its stack: at most three replies rewritten. -/
theorem spliceReplyFrameOutOrSelf (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) :
    SchedLinkFrame st (SeLe4n.Kernel.spliceReplyFrameOutOrSelf st rid) := by
  obtain ⟨m1, m2, h1, h2, h3⟩ := spliceReplyFrameOutOrSelf_store_cases st rid hInv
  have step : ∀ {a b : SystemState}, a.objects.invExt →
      (b = a ∨ ∃ (k : SeLe4n.ReplyId) (o o' : Reply), a.objects[k.toObjId]? = some (.reply o) ∧
        SeLe4n.Model.storeObject k.toObjId (.reply o') a = .ok ((), b)) →
      b.objects.invExt ∧ SchedLinkFrame a b := by
    intro a b hA h
    rcases h with rfl | ⟨k, o, o', hO, hS⟩
    · exact ⟨hA, .refl _⟩
    · exact ⟨storeObject_preserves_objects_invExt a b _ _ hA hS, storeReplyOver hA hO hS⟩
  have f1 := step hInv h1
  have f2 := step f1.1 h2
  exact f1.2.trans (f2.2.trans (step f2.1 h3).2)

theorem spliceThreadReplyFrameOut (st : SystemState) (t : TCB) (hInv : st.objects.invExt) :
    SchedLinkFrame st (SeLe4n.Kernel.spliceThreadReplyFrameOut st t) := by
  unfold SeLe4n.Kernel.spliceThreadReplyFrameOut
  cases t.replyObject with
  | none => exact .refl st
  | some rid => exact spliceReplyFrameOutOrSelf st rid hInv

/-- The consume of a caller's reply link: the reply consumed, the caller's link
cleared. -/
theorem consumeCallerReply {st st' : SystemState} {c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (hInv : st.objects.invExt) (h : SystemState.consumeCallerReply c rid st = .ok ((), st')) :
    SchedLinkFrame st st' := by
  unfold SystemState.consumeCallerReply at h
  cases hC : SystemState.consumeReply rid st with
  | error e => rw [hC] at h; cases h
  | ok p =>
    obtain ⟨⟨⟩, st1⟩ := p
    rw [hC] at h
    have f1 : st1.objects.invExt ∧ SchedLinkFrame st st1 := by
      unfold SystemState.consumeReply at hC
      cases hR : st.getReply? rid with
      | none => rw [hR] at hC; cases hC; exact ⟨hInv, .refl _⟩
      | some r =>
        rw [hR] at hC
        exact ⟨storeObject_preserves_objects_invExt _ _ _ _ hInv hC,
          storeReplyOver hInv ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) hC⟩
    simp only at h
    cases hT : st1.getTcb? c with
    | none => rw [hT] at h; cases h; exact f1.2
    | some tcb =>
      rw [hT] at h
      have hPre := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
      exact f1.2.trans (storeObject f1.1 h (by rw [hPre]; rfl) (by rw [hPre]; rfl)
        (by rw [hPre]; rfl))

theorem consumeReplyLink (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (hInv : st.objects.invExt) :
    SchedLinkFrame st (Lifecycle.Suspend.consumeReplyLink st c t) := by
  unfold Lifecycle.Suspend.consumeReplyLink
  split
  · exact .refl st
  · rename_i rid _
    exact consumeCallerReply hInv (SystemState.consumeCallerReply_eq_link st c rid)

/-- **A reply-blocked caller's cancel after its donation return**: the splice,
the restore, the consume and the unlink write none of what the invariants
read. -/
theorem replyCancelTail (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (hInv : st.objects.invExt) :
    SchedLinkFrame st (SystemState.unlinkReplyWaiterOpt
        (Lifecycle.Suspend.consumeReplyLink
          (Lifecycle.Suspend.restoreToReadyCancelled (SeLe4n.Kernel.spliceThreadReplyFrameOut st t)
            c) c t)
        c t.blockingServer?) := by
  have g1 := FinaliseFrameAny.spliceThreadReplyFrameOut st t hInv
  have f1 := spliceThreadReplyFrameOut st t hInv
  have f2 : SchedLinkFrame st (Lifecycle.Suspend.restoreToReadyCancelled
      (SeLe4n.Kernel.spliceThreadReplyFrameOut st t) c) := by
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    exact f1.trans (updateTcb _ c _ g1.invExt)
  have g2 : (Lifecycle.Suspend.restoreToReadyCancelled
      (SeLe4n.Kernel.spliceThreadReplyFrameOut st t) c).objects.invExt := by
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    exact SystemState.updateTcb_preserves_objects_invExt _ _ _ g1.invExt
  have f3 := f2.trans (consumeReplyLink _ c t g2)
  refine f3.trans (of_agreeOffRunLinks
    (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks _ c _) ?_)
  rw [SystemState.unlinkReplyWaiterOpt_eq_objects]

end SchedLinkFrame

/-- **A reply-blocked caller's cancel with its loan handed back keeps every
scheduling-link invariant**: the donation return moves one binding pair
(`returnDonationToCancelledCaller_preserves_schedLinks`); the splice, restore,
consume and unlink after it write none of what the invariants read
(`SchedLinkFrame.replyCancelTail`); the migration moves the returned context's
replenishments to its new holder's home, which is what re-establishes their
affinity (`cancelIpcBlockingMigrated_establishes_replenishQueueAffinityConsistent_smp`)
and keeps them bound; the holder's deschedule and the boost revert are frames. -/
theorem finaliseReplyCancel_preserves_schedContextLinkInvariant {s : SystemState}
    {c : SeLe4n.ThreadId} {t : TCB} {ep : SeLe4n.ObjId} {rt : Option SeLe4n.ThreadId}
    (hInv : s.objects.invExt) (hI : schedContextLinkInvariant s)
    (hB : t.ipcState = .blockedOnReply ep rt) :
    schedContextLinkInvariant
      (finaliseReplyRevert (cancelIpcBlockingReclaimed c t s) t.blockingServer?) := by
  obtain ⟨bR, cR, qR⟩ := returnDonationToCancelledCaller_preserves_schedLinks s c t hInv
    hI.budgets hI.binding hI.replenishBound
  have gR := FinaliseFrameAny.returnDonationToCancelledCaller s c t hInv
  have hEq := cancelIpcBlocking_replyArm_unfold s c t hB
  have F := SchedLinkFrame.replyCancelTail _ c t gR.invExt
  rw [← hEq] at F
  have hInvC : (Lifecycle.Suspend.cancelIpcBlocking s c t).objects.invExt :=
    (FinaliseFrameAny.replyCancel s c t hInv hB).invExt
  -- The migration: objects kept off the release links, the replenishments moved.
  have hObjM := cancelIpcBlockingMigrated_agree c t s
  have bM : allTimeoutBudgetsNone (cancelIpcBlockingMigrated c t s) :=
    allTimeoutBudgetsNone_of_aux (schedAuxAgree.of_objectsAgreeOffReleaseLinks hObjM)
      (allTimeoutBudgetsNone_of_aux F.aux bR)
  have cM : schedContextBindingConsistent (cancelIpcBlockingMigrated c t s) :=
    schedContextBindingConsistent_of_binding
      (fun o => proj_eq_of_map_eq _ _ (fun x => by cases x <;> rfl) (hObjM o))
      (schedContextBindingConsistent_of_binding F.binding cR)
  have rC : (Lifecycle.Suspend.cancelIpcBlocking s c t).releaseQueueRefined :=
    F.releaseState.refined
      ((returnDonationToCancelledCaller_releaseStateAgree s c t hInv).refined hI.refined)
  have rM : (cancelIpcBlockingMigrated c t s).releaseQueueRefined := by
    unfold cancelIpcBlockingMigrated
    split
    · exact migrateSchedContextReplenishment_refined rC _ _ _
    · exact rC
  have qC := replenishQueueEntriesBound_smp_of_frame F.binding F.replenish qR
  have qM : replenishQueueEntriesBound_smp (cancelIpcBlockingMigrated c t s) := by
    unfold cancelIpcBlockingMigrated
    split
    · exact migrateSchedContextReplenishment_preserves_replenishQueueEntriesBound_smp _ _ _ _ qC
    · exact qC
  have hM : schedContextLinkInvariant (cancelIpcBlockingMigrated c t s) :=
    ⟨bM, cM, qM, cancelIpcBlockingMigrated_establishes_replenishQueueAffinityConsistent_smp c t s
      hInv hI.replenishAffinity, rM⟩
  -- The holder's deschedule and the revert.
  have FD : SchedLinkFrame (cancelIpcBlockingMigrated c t s) (cancelIpcBlockingReclaimed c t s) :=
    SchedLinkFrame.of_agreeOffRunLinks
      (descheduleUnboundHolder_objectsAgreeOffRunLinks s (cancelIpcBlockingMigrated c t s) c t)
      (by unfold cancelIpcBlockingReclaimed descheduleUnboundHolder; split
          · rfl
          · exact descheduleAtPlacement_releaseSlots _ _)
  exact (SchedLinkFrame.finaliseReplyRevert _ t.blockingServer?
    (cancelIpcBlockingReclaimed_objects_invExt c t s hInvC)).preserves (FD.preserves hM)

-- ============================================================================
-- §8  The finalisation
-- ============================================================================

/-- **WS-ZA ZA6.6: a step that writes the yield writes alone is a frame**: a
thread's yield-to code and return registers and a context's yield-from code
and consumed count are none of the fields the scheduling-link invariants read. -/
theorem SchedLinkFrame.of_objectsAgreeOffYield {st st' : SystemState}
    (hA : st'.objectsAgreeOffYield st) (hS : st'.scheduler = st.scheduler) :
    SchedLinkFrame st st' := by
  have key : ∀ {α : Type} (p : Option KernelObject → α),
      (∀ o, p (some o.withoutYield) = p (some o)) →
      ∀ oid : SeLe4n.ObjId, p st'.objects[oid]? = p st.objects[oid]? := by
    intro α p hp oid
    have hp' : ∀ x : Option KernelObject, p (x.map KernelObject.withoutYield) = p x := by
      intro x; cases x
      · rfl
      · exact hp _
    rw [← hp' st'.objects[oid]?, hA oid, hp']
  exact ⟨key _ (fun o => by cases o <;> rfl), key _ (fun o => by cases o <;> rfl),
    key _ (fun o => by cases o <;> rfl), by rw [hS]⟩

/-- The yield steps of a finalisation, as the closure asks them. -/
theorem SchedLinkFrame.yieldStep :
    FinaliseYieldStep (fun s => s.objects.invExt ∧ schedContextLinkInvariant s) :=
  ⟨fun s t h => ⟨SystemState.cancelYieldTo_preserves_objects_invExt _ _ h.1,
      (SchedLinkFrame.of_objectsAgreeOffYield (SystemState.cancelYieldTo_objectsAgreeOffYield s t h.1)
        (SystemState.cancelYieldTo_scheduler s t)).preserves h.2⟩,
   fun s c h => ⟨SystemState.completeYieldFrom_preserves_objects_invExt _ _ h.1,
      (SchedLinkFrame.of_objectsAgreeOffYield
        (SystemState.completeYieldFrom_objectsAgreeOffYield s c h.1)
        (SystemState.completeYieldFrom_scheduler s c)).preserves h.2⟩⟩

/-- **The finalisation keeps every scheduling-link invariant**, every step of
it (`finaliseFinalObject_closed`): each step a frame (`SchedLinkFrame`) but the
context's release of its holder
(`finaliseScRelease_preserves_schedContextLinkInvariant`) and the reply's caller
cancel (`finaliseReplyCancel_preserves_schedContextLinkInvariant`). -/
theorem finaliseFinalObject_preserves_schedContextLinkInvariant (target : Nat) (st : SystemState)
    (hInv : st.objects.invExt) (h : schedContextLinkInvariant st) :
    schedContextLinkInvariant (finaliseFinalObject target st) :=
  (finaliseFinalObject_closed (fun s => s.objects.invExt ∧ schedContextLinkInvariant s)
    (fun e q s _ t tcb h _ _ _ _ =>
      ⟨(FinaliseFrame.storeEndpointWaiterCancelled s e q t tcb.queueNext h.1).invExt,
        (SchedLinkFrame.storeEndpointWaiterCancelled s e q t tcb.queueNext h.1).preserves h.2⟩)
    (fun n s _ t tcb h _ _ _ hC =>
      have hB := notificationWaiterCancellable_blocked hC
      have F := FinaliseFrame.notificationCancel s t tcb n h.1 hB
      ⟨(F.trans (FinaliseFrame.wakeCancelledWaiter _ t F.invExt)).invExt,
        ((SchedLinkFrame.notificationCancel s t tcb n h.1 hB).trans
          (SchedLinkFrame.wakeCancelledWaiter _ t F.invExt)).preserves h.2⟩)
    (fun n s _ t h _ _ _ _ =>
      ⟨(FinaliseFrame.storeUnbindNotification s t n h.1).invExt,
        (SchedLinkFrame.storeUnbindNotification s t n h.1).preserves h.2⟩)
    (fun s t _ h _ _ _ _ =>
      ⟨(FinaliseFrame.descheduleAt s t _ h.1).invExt,
        (SchedLinkFrame.descheduleAtPlacement s t).preserves h.2⟩)
    (fun _ _ _ _ _ _ h hT hS hSc hB hOk =>
      ⟨(FinaliseFrame.cancelBoundDonationOnCore h.1 hOk).invExt,
        finaliseScRelease_preserves_schedContextLinkInvariant h.1 h.2 hT hS hSc hB hOk⟩)
    (fun s n t tcb _ h _ hI _ _ =>
      ⟨(FinaliseFrame.notificationCancel s t tcb n h.1 hI).invExt,
        (SchedLinkFrame.notificationCancel s t tcb n h.1 hI).preserves h.2⟩)
    (fun s e q t ep tcb h _ _ _ =>
      ⟨(FinaliseFrame.storeEndpointBlockedCancelled s e q t ep tcb h.1).invExt,
        (SchedLinkFrame.storeEndpointBlockedCancelled s e q t ep tcb h.1).preserves h.2⟩)
    (fun s t _ h _ _ _ _ _ =>
      ⟨(FinaliseFrame.suspend s t h.1).invExt, (SchedLinkFrame.suspend s t h.1).preserves h.2⟩)
    (fun s t h =>
      ⟨(FinaliseFrame.releaseCores s t h.1).invExt, (SchedLinkFrame.releaseCores s t).preserves h.2⟩)
    (fun _ _ _ _ _ _ h _ _ hR _ hS _ _ _ _ =>
      ⟨(FinaliseFrameAny.unstack h.1 hR hS).invExt, (SchedLinkFrame.unstack h.1 hR hS).preserves h.2⟩)
    (fun s x r c t h hX hC hT hF =>
      have hB := (replyCallerFinalisable_parts hF).2.2.2.2.1
      ⟨(FinaliseFrameAny.replyStep s s x r c t (.refl h.1) hX hC hT hF).invExt,
        finaliseReplyCancel_preserves_schedContextLinkInvariant h.1 h.2 hB.choose_spec.choose_spec⟩)
    (fun s _ _ tid _ h _ _ e => e ▸
      ⟨SystemState.updateTcb_preserves_objects_invExt _ _ _ h.1,
        (SchedLinkFrame.updateTcb s tid _ h.1).preserves h.2⟩)
    SchedLinkFrame.yieldStep target st ⟨hInv, h⟩).2

-- ============================================================================
-- §9  The retire
-- ============================================================================

/-- A context after the retire is the context before it. -/
theorem retireFinalObject_schedContext_back (ec : CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {o : SeLe4n.ObjId} {sc : SchedContext}
    (h : (retireFinalObject ec target recorder st).objects[o]? = some (.schedContext sc)) :
    st.objects[o]? = some (.schedContext sc) :=
  retireFinalObject_back ec target recorder st hInv h (fun _ e => KernelObject.noConfusion e)

/-- **The retire keeps every context bound to a thread**: a context it erases
is bound to none. -/
theorem retireFinalObject_schedContext_bound (ec : CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {o : SeLe4n.ObjId} {sc : SchedContext}
    (h : st.objects[o]? = some (.schedContext sc)) {tid : SeLe4n.ThreadId}
    (hb : sc.boundThread = some tid) :
    (retireFinalObject ec target recorder st).objects[o]? = some (.schedContext sc) := by
  rcases retireFinalObject_schedContext_cases ec target recorder st hInv h with e | ⟨-, hR⟩
  · exact e
  · rw [schedContextRetirable_boundThread hR h] at hb; cases hb

/-- **The retire keeps every thread bound to a context**: a thread it erases is
quiescent, bound to none. -/
theorem retireFinalObject_tcb_named (ec : CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {oid : SeLe4n.ObjId} {t : TCB}
    (h : st.objects[oid]? = some (.tcb t)) {s : SeLe4n.SchedContextId}
    (hb : t.schedContextBinding.scId? = some s) :
    (retireFinalObject ec target recorder st).objects[oid]? = some (.tcb t) := by
  rcases retireFinalObject_tcb_kept_or_quiescent ec target recorder st hInv h with e | ⟨-, -, -, hQ, -⟩
  · rw [e, h]
  · have hc := (threadQuiescent_codes hQ).2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [TCB.scBindingScCode_of_names hb] at hc; cases hc

/-- **The final-delete retire keeps every queued context bound**: the scheduler
is kept, and a context the retire erases is bound to no thread, so a context a
core's replenishment queue holds — bound, by the invariant — is one the retire
keeps.  So the guard reads no replenishment queue. -/
theorem retireFinalObject_preserves_replenishQueueEntriesBound_smp (ec : CoreId)
    (target recorder : Nat) (st : SystemState) (hInv : st.objects.invExt)
    (h : replenishQueueEntriesBound_smp st) :
    replenishQueueEntriesBound_smp (retireFinalObject ec target recorder st) := by
  intro c s0 n hMem
  rw [(retireFinalObject_fields ec target recorder st).2.1] at hMem
  obtain ⟨sc, hS, tid, hb⟩ := h c s0 n hMem
  refine ⟨sc, (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr ?_, tid, hb⟩
  exact retireFinalObject_schedContext_bound ec target recorder st hInv
    ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hS) hb

/-- **The final-delete retire keeps every scheduling-link invariant**: it keeps
the scheduler and every thread's budget, and it erases a thread only bound to
no context and a context only bound to no thread, so no binding loses its
partner and no queued context its home. -/
theorem retireFinalObject_preserves_schedContextLinkInvariant (ec : CoreId)
    (target recorder : Nat) (st : SystemState) (hInv : st.objects.invExt)
    (h : schedContextLinkInvariant st) :
    schedContextLinkInvariant (retireFinalObject ec target recorder st) := by
  have hSch := (retireFinalObject_fields ec target recorder st).2.1
  have hBack := fun {o : SeLe4n.ObjId} {t : TCB} (e : (retireFinalObject ec target recorder st).objects[o]? = some (.tcb t)) =>
    retireFinalObject_tcb_back ec target recorder st hInv e
  have hCons : schedContextBindingConsistent (retireFinalObject ec target recorder st) := by
    refine ⟨fun tid tcb hT s hb => ?_, fun s sc hS y hy => ?_⟩
    · obtain ⟨sc, hsc, hbt⟩ := h.binding.1 tid tcb (hBack hT) s hb
      exact ⟨sc, retireFinalObject_schedContext_bound ec target recorder st hInv hsc hbt, hbt⟩
    · have hS' := retireFinalObject_schedContext_back ec target recorder st hInv hS
      obtain ⟨ty, hty, hbb⟩ := h.binding.2 s sc hS' y hy
      refine ⟨ty, retireFinalObject_tcb_named ec target recorder st hInv hty (s := s) ?_, hbb⟩
      rcases hbb with e | ⟨_, e⟩ <;> rw [e] <;> rfl
  refine ⟨fun tid tcb hT => h.budgets tid tcb (hBack hT), hCons,
    retireFinalObject_preserves_replenishQueueEntriesBound_smp ec target recorder st hInv
      h.replenishBound, fun c s0 n hMem sc hS tid hb => ?_,
    (retireFinalObject_releaseStateAgree ec target recorder st hInv).refined h.refined⟩
  rw [hSch] at hMem
  have hS' := retireFinalObject_schedContext_back ec target recorder st hInv
    ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hS)
  have hc := h.replenishAffinity c s0 n hMem sc
    ((SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hS') tid hb
  obtain ⟨ty, hty, hbb⟩ := h.binding.2 s0 sc hS' tid hb
  have hKeep := retireFinalObject_tcb_named ec target recorder st hInv hty (s := s0)
    (by rcases hbb with e | ⟨_, e⟩ <;> rw [e] <;> rfl)
  rw [← hc]
  unfold determineTargetCore SystemState.getTcb?
  rw [hKeep, hty]

-- ============================================================================
-- §10  The slot delete, the page teardown and a thread slot's set
-- ============================================================================

namespace SchedLinkFrame

/-- A run of slot-link writes: links alone, the scheduler untouched. -/
theorem linkReach {st₀ st : SystemState} (h : SystemState.linkReach st₀ st)
    (hInv : st₀.objects.invExt) : SchedLinkFrame st₀ st :=
  of_agreeOffDerivationLinks (h.agree hInv) (by rw [h.fields])

/-- A derivation edge: the tree and the links alone. -/
theorem cdtAddChild (st : SystemState) (p c : SlotRef) (op : DerivationOp)
    (hInv : st.objects.invExt) : SchedLinkFrame st (st.cdtAddChild p c op) :=
  (of_objects_eq (st := st) (st' := { st with cdt := st.cdt.addEdge p c op }) rfl rfl).trans
    (linkReach (SystemState.cdtAddChild_reach st p c op) hInv)

/-- The splice of a deleted slot out of the derivation tree. -/
theorem spliceDeletedCdtNode (st : SystemState) (ref : SlotRef) (hInv : st.objects.invExt) :
    SchedLinkFrame st (SeLe4n.Kernel.spliceDeletedCdtNode st ref) :=
  of_agreeOffDerivationLinks (spliceDeletedCdtNode_agree hInv ref).1
    (by rw [spliceDeletedCdtNode_scheduler])

/-- `.cspaceDelete`: the core delete empties one slot of a CNode or a thread,
which keeps every projection, and the splice writes links alone. -/
theorem cspaceDeleteSlot {st st' : SystemState} {addr : CSpaceAddr} (hInv : st.objects.invExt)
    (hStep : SeLe4n.Kernel.cspaceDeleteSlot addr st = .ok ((), st')) : SchedLinkFrame st st' := by
  obtain ⟨stC, hCore, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' hStep
  refine trans ?_ (spliceDeletedCdtNode stC addr (cspaceDeleteSlotCore_invExt _ _ _ hInv hCore))
  rcases cspaceDeleteSlotCore_ok_cases hCore with ⟨cn, hO, hS⟩ | ⟨t, hO, hS⟩
  · exact storeObject hInv hS (by rw [hO]; rfl) (by rw [hO]; rfl) (by rw [hO]; rfl)
  · exact storeObject hInv hS (by rw [hO]; rfl) (by rw [hO]; rfl) (by rw [hO]; rfl)

/-- A write of VSpace roots alone, the scheduler untouched. -/
theorem of_vspaceRootOnlyWrite {st st' : SystemState} (hW : vspaceRootOnlyWrite st st')
    (hS : st'.scheduler = st.scheduler) : SchedLinkFrame st st' := by
  refine ⟨fun oid => ?_, fun oid => ?_, fun oid => ?_, by rw [hS]⟩
  all_goals
    rcases hW oid with e | ⟨⟨r, hr⟩, ⟨r', hr'⟩⟩
    · rw [e]
    · rw [hr, hr']; rfl

/-- The page teardown after a final delete writes VSpace roots alone. -/
theorem finaliseDestroyedCapabilities {ec : CoreId} {named : List SeLe4n.ObjId}
    {pages : List MappedPage} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.finaliseDestroyedCapabilities ec named pages st = .ok ((), st')) :
    SchedLinkFrame st st' :=
  let hF := finaliseDestroyedCapabilities_ok_frame ec named pages st st' hInv h
  of_vspaceRootOnlyWrite hF.2.1 hF.2.2.1

/-- A thread slot's copy: the slot's delete, the insert of the copied capability
into the thread's space slot, which keeps every projection, and the derivation
edge, which writes links alone. -/
theorem threadSlotCopied {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hInv : st.objects.invExt) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    SchedLinkFrame st (SeLe4n.Kernel.threadSlotCopied st tid slot srcCNode srcSlot rights) := by
  have hD := cspaceDeleteSlot hInv (copyIntoThreadSlot_delete hT slot)
  obtain ⟨-, hI⟩ := threadSlotDeleted_tcb hInv hT slot
  rcases threadSlotCopied_cases st tid slot srcCNode srcSlot rights with ⟨-, e⟩ | ⟨cap, -, e⟩
  · rw [e]; exact hD
  · rw [e]
    have hU := SystemState.updateTcb_preserves_objects_invExt _ tid
      (·.insertSpaceCap slot (TCB.spaceCopyOf cap rights)) hI
    exact hD.trans ((updateTcb _ tid (·.insertSpaceCap slot (TCB.spaceCopyOf cap rights)) hI).trans
      (cdtAddChild _ _ _ _ hU))

end SchedLinkFrame

/-- **The slot delete keeps every scheduling-link invariant.** -/
theorem cspaceDeleteSlot_preserves_schedContextLinkInvariant {st st' : SystemState}
    {addr : CSpaceAddr} (hInv : st.objects.invExt) (h : schedContextLinkInvariant st)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) : schedContextLinkInvariant st' :=
  (SchedLinkFrame.cspaceDeleteSlot hInv hStep).preserves h

/-- **The page teardown keeps every scheduling-link invariant.** -/
theorem finaliseDestroyedCapabilities_preserves_schedContextLinkInvariant {ec : CoreId}
    {named : List SeLe4n.ObjId} {pages : List MappedPage} {st st' : SystemState}
    (hInv : st.objects.invExt) (h : schedContextLinkInvariant st)
    (hStep : finaliseDestroyedCapabilities ec named pages st = .ok ((), st')) :
    schedContextLinkInvariant st' :=
  (SchedLinkFrame.finaliseDestroyedCapabilities hInv hStep).preserves h

/-- **A thread space slot's set keeps every scheduling-link invariant**: the
copy writes none of what they read, and the retire after it keeps them
(`retireFinalObject_preserves_schedContextLinkInvariant`). -/
theorem threadSlotSet_preserves_schedContextLinkInvariant (ec : CoreId) {st : SystemState}
    {tid : SeLe4n.ThreadId} {t : TCB} (hInv : st.objects.invExt) (h : schedContextLinkInvariant st)
    (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot) (srcCNode : SeLe4n.ObjId)
    (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    schedContextLinkInvariant (threadSlotSet ec st tid slot srcCNode srcSlot rights) := by
  unfold threadSlotSet
  exact retireFinalObject_preserves_schedContextLinkInvariant ec _ _ _
    (threadSlotCopied_tcb hInv hT slot srcCNode srcSlot rights).2
    ((SchedLinkFrame.threadSlotCopied hInv hT slot srcCNode srcSlot rights).preserves h)

/-- **A thread space slot's set keeps every thread's budget clear**: the copy
writes no budget, and a thread the retire keeps is a thread of the copy. -/
theorem threadSlotSet_preserves_allTimeoutBudgetsNone (ec : CoreId) {st : SystemState}
    {tid : SeLe4n.ThreadId} {t : TCB} (hInv : st.objects.invExt)
    (hBudgets : allTimeoutBudgetsNone st) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    allTimeoutBudgetsNone (threadSlotSet ec st tid slot srcCNode srcSlot rights) := by
  unfold threadSlotSet
  intro tid' tcb hT'
  exact allTimeoutBudgetsNone_of_aux (SchedLinkFrame.threadSlotCopied hInv hT slot srcCNode
    srcSlot rights).aux hBudgets tid' tcb (retireFinalObject_tcb_back ec _ _ _
      (threadSlotCopied_tcb hInv hT slot srcCNode srcSlot rights).2 hT')

/-- **A thread space slot's set preserves the IPC bundle**: the copy does
(`threadSlotCopied_preserves_ipcInvariantFull`), and so does the retire after it
(`retireFinalObject_preserves_ipcInvariantFull`), on the copy's budgets, which
are the pre-state's. -/
theorem threadSlotSet_preserves_ipcInvariantFull (ec : CoreId) {st : SystemState}
    {tid : SeLe4n.ThreadId} {t : TCB} (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hBudgets : allTimeoutBudgetsNone st) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    ipcInvariantFull (threadSlotSet ec st tid slot srcCNode srcSlot rights) ∧
      (threadSlotSet ec st tid slot srcCNode srcSlot rights).objects.invExt := by
  unfold threadSlotSet
  exact retireFinalObject_preserves_ipcInvariantFull ec _ _ _
    (threadSlotCopied_tcb hObjInv hT slot srcCNode srcSlot rights).2
    (threadSlotCopied_preserves_ipcInvariantFull hObjInv hInv hT slot srcCNode srcSlot rights)
    (allTimeoutBudgetsNone_of_aux
      (SchedLinkFrame.threadSlotCopied hObjInv hT slot srcCNode srcSlot rights).aux hBudgets)

/-- **WS-BP BP7.1 (`v0.36.11`)**: a space change preserves the IPC bundle — each
slot set does (`threadSlotSet_preserves_ipcInvariantFull`). -/
theorem copyThreadSpaces_preserves_ipcInvariantFull (ec : CoreId)
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (cnSrc vrSrc : CSpaceAddr)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hBudgets : allTimeoutBudgetsNone st)
    (hStep : copyThreadSpaces ec st vtid cnSrc vrSrc = .ok st') :
    ipcInvariantFull st' := by
  obtain ⟨tcb, hT, -, -, hCn, -, rfl⟩ := copyThreadSpaces_ok hStep
  obtain ⟨cnCap, -, hCL, -⟩ := cspaceRootSourceAdmitted_spec hCn
  obtain ⟨t1, hT1'⟩ := Option.isSome_iff_exists.mp
    (threadSlotSet_getTcb? ec hObjInv hT (slot := TCB.cspaceRootSlot) (by decide)
      cnSrc.cnode cnSrc.slot TCB.cspaceRootRights hCL)
  obtain ⟨h1, hI1⟩ := threadSlotSet_preserves_ipcInvariantFull ec hObjInv hInv hBudgets hT
    TCB.cspaceRootSlot cnSrc.cnode cnSrc.slot TCB.cspaceRootRights
  exact (threadSlotSet_preserves_ipcInvariantFull ec hI1 h1
    (threadSlotSet_preserves_allTimeoutBudgetsNone ec hObjInv hBudgets hT _ _ _ _) hT1'
    _ _ _ _).1

/-- **A space change keeps every scheduling-link invariant** — each slot set
does (`threadSlotSet_preserves_schedContextLinkInvariant`). -/
theorem copyThreadSpaces_preserves_schedContextLinkInvariant (ec : CoreId)
    {st st' : SystemState} {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr}
    (hInv : st.objects.invExt) (h : schedContextLinkInvariant st)
    (hStep : copyThreadSpaces ec st vtid cnSrc vrSrc = .ok st') :
    schedContextLinkInvariant st' := by
  obtain ⟨tcb, hT, -, -, hCn, -, rfl⟩ := copyThreadSpaces_ok hStep
  obtain ⟨cnCap, -, hCL, -⟩ := cspaceRootSourceAdmitted_spec hCn
  obtain ⟨t1, hT1'⟩ := Option.isSome_iff_exists.mp
    (threadSlotSet_getTcb? ec hInv hT (slot := TCB.cspaceRootSlot) (by decide)
      cnSrc.cnode cnSrc.slot TCB.cspaceRootRights hCL)
  have hI1 : (threadSlotSet ec st vtid.val TCB.cspaceRootSlot cnSrc.cnode cnSrc.slot
      TCB.cspaceRootRights).objects.invExt := by
    unfold threadSlotSet
    exact (retireFinalObject_frame ec _ _ _ (threadSlotCopied_tcb hInv hT TCB.cspaceRootSlot
      cnSrc.cnode cnSrc.slot TCB.cspaceRootRights).2).1
  exact threadSlotSet_preserves_schedContextLinkInvariant ec hI1
    (threadSlotSet_preserves_schedContextLinkInvariant ec hInv h hT _ _ _ _) hT1' _ _ _ _

end SeLe4n.Kernel
