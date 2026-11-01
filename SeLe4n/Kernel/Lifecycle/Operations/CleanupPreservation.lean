-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.Cleanup
import SeLe4n.Kernel.Architecture.PageTableInstall
-- WS-SM SM6.E: `returnDonatedSchedContext_preserves_objects_invExt` (AI4-A),
-- consumed by `cleanupDonatedSchedContext_preserves_objects_invExt`.
import SeLe4n.Kernel.IPC.Invariant.Defs

/-!
AN4-G.5 (LIF-M05) child module extracted from
`SeLe4n.Kernel.Lifecycle.Operations`. Contains the cleanup-primitive
preservation theorems, the `detachCNodeSlots` helper, the composite
`lifecyclePreRetypeCleanup` pipeline and the named `lifecycleCleanupPipeline`
wrapper (AN4-G.2). Private helpers are promoted to file-boundary scope so the
sibling `ScrubAndUntyped` and `RetypeWrappers` modules can reference them.

The pipeline is an object's destroy step.  The in-place retype that ran it was
retired at WS-ZA ZA5.4 part 14 (every object is carved from an untyped), so no
transition runs it now; it is kept for seL4's `finaliseCap` on a kernel
object's final delete, which reuses it (`docs/planning/UNTYPED_RESET_PLAN.md`,
part 24; `docs/REGISTERED_DEBT.md`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)

-- ============================================================================
-- R4-A: Cleanup preservation theorems
-- ============================================================================

/-- W6-B: spliceOutMidQueueNode only modifies `objects`, preserving all other
    state fields. Bundles the scheduler and lifecycle preservation proofs
    into a single conjunction. -/
theorem spliceOutMidQueueNode_preserves
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (spliceOutMidQueueNode st tid).scheduler = st.scheduler ∧
    (spliceOutMidQueueNode st tid).lifecycle = st.lifecycle := by
  refine ⟨?_, ?_⟩ <;> (unfold spliceOutMidQueueNode; split <;> rfl)

/-- T5-E: spliceOutMidQueueNode preserves the scheduler. -/
theorem spliceOutMidQueueNode_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (spliceOutMidQueueNode st tid).scheduler = st.scheduler :=
  (spliceOutMidQueueNode_preserves st tid).1

/-- T5-E: spliceOutMidQueueNode preserves lifecycle metadata. -/
theorem spliceOutMidQueueNode_lifecycle_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (spliceOutMidQueueNode st tid).lifecycle = st.lifecycle :=
  (spliceOutMidQueueNode_preserves st tid).2

/-- WS-SM SM7.B: spliceOutMidQueueNode only modifies `objects` — the
TLB-shootdown state is framed (`pendingBounded` bundle-carriage leaf). -/
theorem spliceOutMidQueueNode_tlbShootdown_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (spliceOutMidQueueNode st tid).tlbShootdown = st.tlbShootdown := by
  unfold spliceOutMidQueueNode; split <;> rfl

/-- WS-SM SM8.B: spliceOutMidQueueNode only modifies `objects` — the machine
(and hence every core's register bank) is framed.  The information-flow
counterpart of `spliceOutMidQueueNode_scheduler_eq`: per-core confinement reads
the register banks as well as the scheduler slots, so the scheduler frame alone
does not bound a step's observable writes. -/
theorem spliceOutMidQueueNode_machine_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (spliceOutMidQueueNode st tid).machine = st.machine := by
  unfold spliceOutMidQueueNode; split <;> rfl

/-- W6-B: removeFromAllEndpointQueues only modifies `objects`, preserving
    scheduler and lifecycle simultaneously. Reduces redundancy from
    near-identical proofs to a single bundled theorem. -/
theorem removeFromAllEndpointQueues_preserves
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllEndpointQueues st tid).scheduler = st.scheduler ∧
    (removeFromAllEndpointQueues st tid).lifecycle = st.lifecycle := by
  -- AN4-G.5 (LIF-M05): Apply `fold_preserves` directly against the whole
  -- pair invariant, seeded from the splice-preservation witness for the
  -- two fields we care about. Avoids the former `epFold` intermediate,
  -- which relied on syntactic `let ep' : Endpoint := ...` matching that
  -- reshaped to `have` when the def was imported from a sibling child
  -- module. Proving both conjuncts at once in a bundled fold keeps
  -- the proof robust across the AN4-G.5 file-split boundary.
  have hSplice := spliceOutMidQueueNode_preserves st tid
  unfold removeFromAllEndpointQueues
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves
    (spliceOutMidQueueNode st tid).objects (spliceOutMidQueueNode st tid) _
    (fun acc => acc.scheduler = st.scheduler ∧
                acc.lifecycle = st.lifecycle)
    hSplice
    (fun acc _ _ hAcc => by
      split <;> first | exact hAcc | (split <;> first | exact hAcc | (split <;> exact hAcc)))

/-- R4-A.1 + T5-E: removeFromAllEndpointQueues preserves the scheduler. -/
theorem removeFromAllEndpointQueues_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllEndpointQueues st tid).scheduler = st.scheduler :=
  (removeFromAllEndpointQueues_preserves st tid).1

/-- R4-A.1 + T5-E: removeFromAllEndpointQueues preserves lifecycle metadata. -/
theorem removeFromAllEndpointQueues_lifecycle_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllEndpointQueues st tid).lifecycle = st.lifecycle :=
  (removeFromAllEndpointQueues_preserves st tid).2

/-- WS-SM SM7.B: removeFromAllEndpointQueues only modifies `objects` — the
TLB-shootdown state is framed.  Same fold-preservation argument as
`removeFromAllEndpointQueues_preserves`, seeded from the splice frame. -/
theorem removeFromAllEndpointQueues_tlbShootdown_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllEndpointQueues st tid).tlbShootdown = st.tlbShootdown := by
  have hSplice := spliceOutMidQueueNode_tlbShootdown_eq st tid
  unfold removeFromAllEndpointQueues
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves
    (spliceOutMidQueueNode st tid).objects (spliceOutMidQueueNode st tid) _
    (fun acc => acc.tlbShootdown = st.tlbShootdown)
    hSplice
    (fun acc _ _ hAcc => by
      split <;> first | exact hAcc | (split <;> first | exact hAcc | (split <;> exact hAcc)))

/-- WS-SM SM8.B: removeFromAllEndpointQueues only modifies `objects` — the
machine is framed.  Same fold-preservation argument as
`removeFromAllEndpointQueues_tlbShootdown_eq`, seeded from the splice frame. -/
theorem removeFromAllEndpointQueues_machine_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllEndpointQueues st tid).machine = st.machine := by
  have hSplice := spliceOutMidQueueNode_machine_eq st tid
  unfold removeFromAllEndpointQueues
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves
    (spliceOutMidQueueNode st tid).objects (spliceOutMidQueueNode st tid) _
    (fun acc => acc.machine = st.machine)
    hSplice
    (fun acc _ _ hAcc => by
      split <;> first | exact hAcc | (split <;> first | exact hAcc | (split <;> exact hAcc)))

/-- Both branches of a conditional state satisfy `P`, so the conditional does. -/
theorem ite_of_both {P : SystemState → Prop} {a b : SystemState} (c : Prop) [Decidable c]
    (ha : P a) (hb : P b) : P (if c then a else b) := by
  split <;> assumption

/-- WS-ZA ZA4.4: the unlink writes `objects` and nothing else — one
notification and at most two neighbour TCBs, each a record update of the state's
object store.  Every component frame below is read off this. -/
theorem removeFromNotificationWaitQueue_eq_objects (st : SystemState) (tid : SeLe4n.ThreadId) :
    ∃ objs, removeFromNotificationWaitQueue st tid = { st with objects := objs } := by
  have hU : ∀ (s : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB),
      (∃ objs, s = { st with objects := objs }) →
      ∃ objs, s.updateTcb t f = { st with objects := objs } := by
    rintro s t f ⟨o, rfl⟩
    unfold SystemState.updateTcb
    split
    · exact ⟨_, rfl⟩
    · exact ⟨o, rfl⟩
  have hN : ∀ (s : SystemState) prev next, (∃ objs, s = { st with objects := objs }) →
      ∃ objs, unlinkNtfnNeighbours s prev next = { st with objects := objs } := by
    intro s prev next hs
    unfold unlinkNtfnNeighbours
    cases prev <;> cases next <;> dsimp only
    · exact hs
    · exact hU _ _ _ hs
    · exact hU _ _ _ hs
    · exact hU _ _ _ (hU _ _ _ hs)
  unfold removeFromNotificationWaitQueue
  split
  · split
    · split
      · dsimp only
        exact hN _ _ _ (hU _ _ _ ⟨_, rfl⟩)
      · exact ⟨st.objects, rfl⟩
    · exact ⟨st.objects, rfl⟩
  · exact ⟨st.objects, rfl⟩

/-- W6-B: removeFromNotificationWaitQueue only modifies `objects`, preserving
    scheduler and lifecycle simultaneously. -/
theorem removeFromNotificationWaitQueue_preserves
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromNotificationWaitQueue st tid).scheduler = st.scheduler ∧
    (removeFromNotificationWaitQueue st tid).lifecycle = st.lifecycle := by
  obtain ⟨_, h⟩ := removeFromNotificationWaitQueue_eq_objects st tid
  rw [h]; exact ⟨rfl, rfl⟩

/-- WS-SM SM8.B: removeFromNotificationWaitQueue only modifies `objects` —
the machine is framed. -/
theorem removeFromNotificationWaitQueue_machine_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromNotificationWaitQueue st tid).machine = st.machine := by
  obtain ⟨_, h⟩ := removeFromNotificationWaitQueue_eq_objects st tid
  rw [h]

/-- R4-A.2: removeFromNotificationWaitQueue preserves the scheduler. -/
theorem removeFromNotificationWaitQueue_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromNotificationWaitQueue st tid).scheduler = st.scheduler :=
  (removeFromNotificationWaitQueue_preserves st tid).1

/-- R4-A.2: removeFromNotificationWaitQueue preserves lifecycle metadata. -/
theorem removeFromNotificationWaitQueue_lifecycle_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromNotificationWaitQueue st tid).lifecycle = st.lifecycle :=
  (removeFromNotificationWaitQueue_preserves st tid).2

/-- WS-SM SM7.B: removeFromNotificationWaitQueue only modifies `objects`
— the TLB-shootdown state is framed. -/
theorem removeFromNotificationWaitQueue_tlbShootdown_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromNotificationWaitQueue st tid).tlbShootdown = st.tlbShootdown := by
  obtain ⟨_, h⟩ := removeFromNotificationWaitQueue_eq_objects st tid
  rw [h]

/-- WS-SM SM7.B: the composed TCB reference scrub only modifies scheduler
and `objects` — the TLB-shootdown state is framed. -/
theorem cleanupTcbReferences_tlbShootdown_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cleanupTcbReferences st tid).tlbShootdown = st.tlbShootdown := by
  unfold cleanupTcbReferences
  rw [removeFromNotificationWaitQueue_tlbShootdown_eq,
      removeFromAllEndpointQueues_tlbShootdown_eq]
  -- Via the sweep's own frame.  Reducing through `removeRunnableFromAllCores`
  -- here would have to whnf the per-core guard at every core.
  exact removeRunnableFromAllCores_tlbShootdown st tid

-- ============================================================================
-- WS-SM SM6.E: cleanup primitives preserve `objects.invExt`
-- ============================================================================
-- The per-step Robin-Hood external invariant, needed by the SM6.E
-- cancellation invariant surface (`cancelIpcBlocking_preserves_objects_invExt`
-- composes these with `restoreToReady_invExt`).  Every mutation below is an
-- `objects.insert`, so each step is `RHTable.insert_preserves_invExt` and the
-- store-wide sweeps compose via `RHTable.fold_preserves`.

/-- WS-SM SM6.E: `spliceOutMidQueueNode` preserves `objects.invExt` — the two
link patches (predecessor `queueNext`, successor `queuePrev`) are each a
single conditional `objects.insert`. -/
theorem spliceOutMidQueueNode_preserves_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    (spliceOutMidQueueNode st tid).objects.invExt := by
  unfold spliceOutMidQueueNode
  split
  · exact hInv
  · -- Some-TCB arm: the two link patches are each a conditional insert over
    -- the previous table.  Every match leaf is either the untouched table
    -- (`hInv`) or a chain of at most two `insert`s over it; the cascade
    -- closes leaves with `hInv`, peels `insert`s via
    -- `insert_preserves_invExt`, and splits stuck matches until done.
    dsimp only
    repeat' first
      | exact hInv
      | exact SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ hInv
      | apply SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt
      | split

/-- WS-SM SM6.E: `removeFromAllEndpointQueues` preserves `objects.invExt` —
the splice preserves it, and the endpoint sweep is a fold whose every step
is an `objects.insert`. -/
theorem removeFromAllEndpointQueues_preserves_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    (removeFromAllEndpointQueues st tid).objects.invExt := by
  unfold removeFromAllEndpointQueues
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves
    (spliceOutMidQueueNode st tid).objects (spliceOutMidQueueNode st tid) _
    (fun acc => acc.objects.invExt)
    (spliceOutMidQueueNode_preserves_objects_invExt st tid hInv)
    (fun acc _ _ hAcc => by
      split
      · split
        · split
          · exact SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hAcc
          · exact hAcc
        · exact hAcc
      · exact hAcc)

/-- **WS-RR RR7.22 (residual)**: `a` is `b` with (only) its three intrusive-queue
links rewritten.

Stated as an existential over the three link fields rather than as a list of the
fields that *agree*, which is the derive-don't-enumerate difference: a field added
to `TCB` is covered by construction, where an agreement list would silently stop
mentioning it.

**`v0.35.183` (register row 63)**: declared here rather than beside the *backward*
reading that first consumed it, because the **forward** reading below now concludes
it too.  One relation, both directions: the forward one used to conclude
`cpuAffinity` agreement alone, which is this project's *a field is not the
relation* — the splice's own patches are link rewrites, so every non-link field is
framed by the same fact, and fixing one field meant the next conjunct to need one
(here `schedContextBinding`) had to re-derive the whole case analysis. -/
def tcbQueueLinkRewrite (a b : TCB) : Prop :=
  ∃ qp qpp qn np nn, a = { b with
    queuePrevCode := qp, queuePPrevCode := qpp, queueNextCode := qn,
    ntfnPrevCode := np, ntfnNextCode := nn }

theorem tcbQueueLinkRewrite.refl (a : TCB) : tcbQueueLinkRewrite a a :=
  ⟨a.queuePrevCode, a.queuePPrevCode, a.queueNextCode, a.ntfnPrevCode, a.ntfnNextCode, rfl⟩

theorem tcbQueueLinkRewrite.trans {a b c : TCB}
    (h1 : tcbQueueLinkRewrite a b) (h2 : tcbQueueLinkRewrite b c) :
    tcbQueueLinkRewrite a c := by
  obtain ⟨p1, pp1, n1, np1, nn1, rfl⟩ := h1
  obtain ⟨p2, pp2, n2, np2, nn2, rfl⟩ := h2
  exact ⟨p1, pp1, n1, np1, nn1, rfl⟩

/-- **`v0.35.183`**: a link rewrite agrees on every field but the three links.

The projection form the `Option.map` frames consume, stated once over an
arbitrary `f` rather than once per field: a link rewrite is a record update of
exactly those three, so `f` is fixed by `rfl` after the existential is opened.
The two link-writing updates the splice performs are its instances
(`tcbQueueLinkRewrite_queueUnlinkPredecessor` / `_Successor` below). -/
theorem tcbQueueLinkRewrite.field {α : Type} (f : TCB → α) {a b : TCB}
    (h : tcbQueueLinkRewrite a b) (hf : ∀ (t : TCB) qp qpp qn np nn,
      f { t with
        queuePrevCode := qp, queuePPrevCode := qpp, queueNextCode := qn,
        ntfnPrevCode := np, ntfnNextCode := nn } = f t) :
    f a = f b := by
  obtain ⟨qp, qpp, qn, np, nn, rfl⟩ := h
  exact hf b qp qpp qn np nn

/-- **`v0.35.183`**: the predecessor patch is a link rewrite. -/
theorem tcbQueueLinkRewrite_queueUnlinkPredecessor (removed p : TCB) :
    tcbQueueLinkRewrite (queueUnlinkPredecessor removed p) p :=
  ⟨p.queuePrevCode, p.queuePPrevCode, removed.queueNextCode, p.ntfnPrevCode,
    p.ntfnNextCode, rfl⟩

/-- **`v0.35.183`**: and so is the successor patch. -/
theorem tcbQueueLinkRewrite_queueUnlinkSuccessor (removed n : TCB) :
    tcbQueueLinkRewrite (queueUnlinkSuccessor removed n) n :=
  ⟨removed.queuePrevCode, removed.queuePPrevCode, n.queueNextCode, n.ntfnPrevCode,
    n.ntfnNextCode, rfl⟩

theorem _root_.SeLe4n.Model.tcbNtfnLinkRewrite.toQueueLinkRewrite {a b : TCB} (h : tcbNtfnLinkRewrite a b) :
    tcbQueueLinkRewrite a b := by
  obtain ⟨np, nn, rfl⟩ := h
  exact ⟨b.queuePrevCode, b.queuePPrevCode, b.queueNextCode, np, nn, rfl⟩

/-- WS-ZA ZA4.4: the unlink's notification rewrite is well formed — the head
can only become `none` from a `.waiting` state it then corrects to `.idle`, and
an `.idle` or `.active` notification has no head to replace. -/
theorem notificationQueueWellFormed_unlink (notif : Notification)
    (head' tail' : Option SeLe4n.ThreadId)
    (hHead : notif.waitHead = none → head' = none)
    (hWF : notificationQueueWellFormed notif) :
    notificationQueueWellFormed
      { notif with
          waitHeadCode := SeLe4n.ThreadId.optCode head'
          waitTailCode := SeLe4n.ThreadId.optCode tail'
          state := if notif.state = .waiting ∧ head'.isNone then .idle else notif.state } := by
  have hPB : ∀ st hc tc, (Notification.mk st hc tc notif.hasPendingBadge notif.pendingWord
      notif.pendingWord_cleared notif.boundTCBCode notif.irqBound
      notif.taintTag0 notif.taintTag1 notif.taintTag2 notif.taintTag3 notif.taintTag4 notif.taintTag5 notif.taintTag6 notif.taintTag7 notif.taintCount notif.taintSaturated).pendingBadge = notif.pendingBadge := fun _ _ _ => rfl
  have hWH : ∀ st tc, (Notification.mk st (SeLe4n.ThreadId.optCode head') tc
      notif.hasPendingBadge notif.pendingWord notif.pendingWord_cleared
      notif.boundTCBCode notif.irqBound notif.taintTag0 notif.taintTag1 notif.taintTag2 notif.taintTag3 notif.taintTag4 notif.taintTag5 notif.taintTag6 notif.taintTag7 notif.taintCount notif.taintSaturated).waitHead = head' :=
    fun _ _ => SeLe4n.ThreadId.ofOptCode_optCode head'
  unfold notificationQueueWellFormed at hWF ⊢
  rw [hPB, hWH]
  cases hState : notif.state with
  | idle =>
    simp only [hState] at hWF
    exact ⟨hHead hWF.1, hWF.2⟩
  | waiting =>
    simp only [hState] at hWF
    cases head' with
    | none => exact ⟨rfl, hWF.2⟩
    | some h => exact ⟨Option.some_ne_none h, hWF.2⟩
  | active =>
    simp only [hState] at hWF
    exact ⟨hHead hWF.1, hWF.2⟩

/-- WS-ZA ZA4.4: what the notification unlink may do to one slot of the object
table — nothing, a notification rewritten with its pending badge and bound thread
kept, or a TCB whose intrusive links alone are rewritten (the unlinked waiter's
neighbours). -/
def ntfnUnlinkSlotRel (o o' : Option KernelObject) : Prop :=
  o' = o ∨
  (∃ n n', o = some (.notification n) ∧ o' = some (.notification n') ∧
    n'.pendingBadge = n.pendingBadge ∧ n'.boundTCB = n.boundTCB ∧
    (notificationQueueWellFormed n → notificationQueueWellFormed n')) ∨
  (∃ t t', o = some (.tcb t) ∧ o' = some (.tcb t') ∧ tcbNtfnLinkRewrite t' t)

theorem ntfnUnlinkSlotRel.trans {a b c : Option KernelObject}
    (h1 : ntfnUnlinkSlotRel a b) (h2 : ntfnUnlinkSlotRel b c) : ntfnUnlinkSlotRel a c := by
  rcases h1 with rfl | ⟨n, n', rfl, rfl, hB, hT, hW⟩ | ⟨t, t', rfl, rfl, hR⟩
  · exact h2
  · rcases h2 with rfl | ⟨m, m', hm, rfl, hB2, hT2, hW2⟩ | ⟨u, u', hu, _, _⟩
    · exact Or.inr (Or.inl ⟨n, n', rfl, rfl, hB, hT, hW⟩)
    · cases hm
      exact Or.inr (Or.inl ⟨n, m', rfl, rfl, hB2.trans hB, hT2.trans hT, hW2 ∘ hW⟩)
    · cases hu
  · rcases h2 with rfl | ⟨m, m', hm, _, _, _, _⟩ | ⟨u, u', hu, rfl, hR2⟩
    · exact Or.inr (Or.inr ⟨t, t', rfl, rfl, hR⟩)
    · cases hm
    · cases hu; exact Or.inr (Or.inr ⟨t, u', rfl, rfl, hR2.trans hR⟩)

/-- The unlink's reach from `st`: the table stays well formed and every slot is
related to its pre-state reading. -/
def ntfnUnlinkReach (st s : SystemState) : Prop :=
  s.objects.invExt ∧ ∀ k : SeLe4n.ObjId, ntfnUnlinkSlotRel (st.objects[k]?) (s.objects[k]?)

theorem ntfnUnlinkReach_updateTcb {st s : SystemState} (h : ntfnUnlinkReach st s)
    (p : SeLe4n.ThreadId) (f : TCB → TCB) (hf : ∀ t, tcbNtfnLinkRewrite (f t) t) :
    ntfnUnlinkReach st (s.updateTcb p f) := by
  obtain ⟨hInv, hRel⟩ := h
  cases hG : s.getTcb? p with
  | none => rw [SystemState.updateTcb_eq_self_of_none hG]; exact ⟨hInv, hRel⟩
  | some t =>
    rw [SystemState.updateTcb_eq_of_some hG]
    have hT := (SystemState.getTcb?_eq_some_iff s p t).mp hG
    refine ⟨RHTable_insert_preserves_invExt _ _ _ hInv, fun k => ?_⟩
    simp only [RHTable_getElem?_eq_get?] at hT ⊢
    by_cases hk : p.toObjId = k
    · subst hk
      rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self _ _ _ hInv]
      have := hRel p.toObjId
      simp only [RHTable_getElem?_eq_get?, hT] at this
      exact this.trans (Or.inr (Or.inr ⟨t, f t, rfl, rfl, hf t⟩))
    · rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne _ _ _ _
        (fun hb => hk (eq_of_beq hb)) hInv]
      simpa only [RHTable_getElem?_eq_get?] using hRel k

theorem ntfnUnlinkReach_rewriteNotification {st : SystemState} (hInv : st.objects.invExt)
    (oid : SeLe4n.ObjId) (n n' : Notification)
    (hN : st.objects[oid]? = some (.notification n))
    (hB : n'.pendingBadge = n.pendingBadge) (hT : n'.boundTCB = n.boundTCB)
    (hW : notificationQueueWellFormed n → notificationQueueWellFormed n')
    (hAdm : st.rewriteAdmissible oid (.notification n')) :
    ntfnUnlinkReach st (st.rewriteObject oid (.notification n') hAdm) := by
  refine ⟨SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hInv, fun k => ?_⟩
  by_cases hk : oid = k
  · subst hk
    rw [SystemState.rewriteObject_objects_self _ _ _ _ hInv, hN]
    exact Or.inr (Or.inl ⟨n, n', rfl, rfl, hB, hT, hW⟩)
  · rw [SystemState.rewriteObject_objects_ne _ _ _ _ _ hk hInv]
    exact Or.inl rfl

/-- WS-ZA ZA4.4: the neighbour relink rewrites intrusive links only. -/
theorem ntfnUnlinkReach_unlinkNtfnNeighbours {st s : SystemState} (h : ntfnUnlinkReach st s)
    (prev next : Option SeLe4n.ThreadId) :
    ntfnUnlinkReach st (unlinkNtfnNeighbours s prev next) := by
  have hP : ∀ (u : SystemState) (p : SeLe4n.ThreadId) (c : Nat), ntfnUnlinkReach st u →
      ntfnUnlinkReach st (u.updateTcb p (fun t => { t with ntfnNextCode := c })) :=
    fun u p c hu => ntfnUnlinkReach_updateTcb hu p _
      (fun t => ⟨t.ntfnPrevCode, _, rfl⟩)
  have hN : ∀ (u : SystemState) (p : SeLe4n.ThreadId) (c : Nat), ntfnUnlinkReach st u →
      ntfnUnlinkReach st (u.updateTcb p (fun t => { t with ntfnPrevCode := c })) :=
    fun u p c hu => ntfnUnlinkReach_updateTcb hu p _
      (fun t => ⟨_, t.ntfnNextCode, rfl⟩)
  unfold unlinkNtfnNeighbours
  cases prev <;> cases next <;> dsimp only
  · exact h
  · exact hN _ _ _ h
  · exact hP _ _ _ h
  · exact hN _ _ _ (hP _ _ _ h)

/-- **WS-ZA ZA4.4: the notification unlink in one statement.**  It writes the
waiter's notification (queue ends and the state derived from them) and the
links of at most two neighbouring TCBs; every other slot is untouched. -/
theorem removeFromNotificationWaitQueue_reach (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    ntfnUnlinkReach st (removeFromNotificationWaitQueue st tid) := by
  have hRefl : ntfnUnlinkReach st st := ⟨hInv, fun _ => Or.inl rfl⟩
  unfold removeFromNotificationWaitQueue
  split
  · next tcb _ =>
    split
    · next oid _ =>
      split
      · next notif hN _ =>
        have hN' := (SystemState.getNotification?_eq_some_iff st oid notif).mp hN
        dsimp only
        have hW := notificationQueueWellFormed_unlink notif
          (if notif.waitHead = some tid then tcb.ntfnNext else notif.waitHead)
          (if tcb.ntfnNext.isSome then notif.waitTail
            else if notif.waitHead = some tid then none else tcb.ntfnPrev)
          (fun h => by simp [h])
        have h1 := ntfnUnlinkReach_rewriteNotification hInv oid notif _ hN'
          (by rfl) (by rfl) hW (SystemState.rewriteAdmissible_notification hN _)
        exact ntfnUnlinkReach_unlinkNtfnNeighbours
          (ntfnUnlinkReach_updateTcb h1 tid _ (fun _ => ⟨_, _, rfl⟩)) _ _
      · exact hRefl
    · exact hRefl
  · exact hRefl

/-- WS-SM SM6.E: `removeFromNotificationWaitQueue` preserves
`objects.invExt` — every write of the unlink is an in-place rewrite
(`removeFromNotificationWaitQueue_reach`). -/
theorem removeFromNotificationWaitQueue_preserves_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    (removeFromNotificationWaitQueue st tid).objects.invExt :=
  (removeFromNotificationWaitQueue_reach st tid hInv).1

/-- WS-ZA ZA4.4: closing the gap writes the two neighbours and no other slot. -/
theorem unlinkNtfnNeighbours_objects_off (s : SystemState)
    (prev next : Option SeLe4n.ThreadId) (hInv : s.objects.invExt) (k : SeLe4n.ObjId)
    (hP : ∀ p, prev = some p → p.toObjId ≠ k)
    (hN : ∀ n, next = some n → n.toObjId ≠ k) :
    (unlinkNtfnNeighbours s prev next).objects[k]? = s.objects[k]? := by
  unfold unlinkNtfnNeighbours
  cases prev with
  | none =>
    cases next with
    | none => rfl
    | some n => exact SystemState.updateTcb_objects_ne _ n _ k (hN n rfl) hInv
  | some p =>
    have hInv2 := SystemState.updateTcb_preserves_objects_invExt s p
      (fun t => { t with ntfnNextCode := SeLe4n.ThreadId.optCode next }) hInv
    cases next with
    | none => exact SystemState.updateTcb_objects_ne _ p _ k (hP p rfl) hInv
    | some n =>
      dsimp only
      rw [SystemState.updateTcb_objects_ne _ n _ k (hN n rfl) hInv2]
      exact SystemState.updateTcb_objects_ne _ p _ k (hP p rfl) hInv

/-- WS-ZA ZA4.4: the unlink writes the notification the victim waits on, the
victim itself (its queue links cleared) and the victim's two queue neighbours,
and no other slot. -/
theorem removeFromNotificationWaitQueue_objects_off (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (tcb : TCB)
    (hT : st.getTcb? tid = some tcb) (k : SeLe4n.ObjId)
    (hOff : ∀ oid, tcb.ipcState = .blockedOnNotification oid → oid ≠ k)
    (hV : ∀ oid, tcb.ipcState = .blockedOnNotification oid → tid.toObjId ≠ k)
    (hP : ∀ p, tcb.ntfnPrev = some p → p.toObjId ≠ k)
    (hN : ∀ n, tcb.ntfnNext = some n → n.toObjId ≠ k) :
    (removeFromNotificationWaitQueue st tid).objects[k]? = st.objects[k]? := by
  unfold removeFromNotificationWaitQueue
  simp only [hT]
  cases hS : tcb.ipcState with
  | blockedOnNotification oid =>
    dsimp only
    split
    · have hR : ∀ (n' : Notification) h,
          (st.rewriteObject oid (.notification n') h).objects[k]? = st.objects[k]? :=
        fun n' h => SystemState.rewriteObject_objects_ne st oid k _ h (hOff oid hS) hInv
      refine (unlinkNtfnNeighbours_objects_off _ _ _
        (SystemState.updateTcb_preserves_objects_invExt _ _ _
          (SystemState.rewriteObject_preserves_objects_invExt st oid _ _ hInv)) k ?_ hN).trans
        ((SystemState.updateTcb_objects_ne _ tid _ k (hV oid hS)
          (SystemState.rewriteObject_preserves_objects_invExt st oid _ _ hInv)).trans (hR _ _))
      intro p hp
      split at hp
      · cases hp
      · exact hP p hp
    · rfl
  | _ => rfl

-- ============================================================================
-- WS-SM SM6.E: per-key lookup characterisation of the cleanup sweeps
-- ============================================================================
-- The frame facts the cross-core cancellation composite needs closed-form:
-- a key holding a TCB before the sweep holds a TCB with the **same
-- `cpuAffinity`** afterwards (the sweeps rewrite endpoints/notifications and
-- patch queue-link fields only), and a key holding no TCB never acquires
-- one.  Built on the SM6.E fold keystone
-- (`RHTable.fold_preserves_of_lookup`): the fold step learns the visited
-- key's stored value, so an endpoint-valued visit can never alias a
-- TCB-holding key.

/-- WS-SM SM6.E: re-inserting a rewrite `q` of the TCB `p` read at key `nid`
preserves TCB-kind at every key that held a TCB before the insert, and carries
whatever relation `q` bears to `p` — the single-step frame instantiated by both
`spliceOutMidQueueNode` link patches and by every conditional TCB rewrite in
the suspend teardown (`restoreToReady`, `consumeReplyLink`).

**`v0.35.183` (register row 63): the relation is a PARAMETER.**  It was fixed at
`cpuAffinity` agreement, which is one consequence of what the callers actually
know: the splice's patches are *link rewrites* (`tcbQueueLinkRewrite`), which fix
every non-link field at once, while the suspend teardown's rewrites clear IPC
fields and genuinely agree on the affinity alone.  Two different relations, one
question — so the relation is the argument, and `motive` need only be reflexive,
because at every key the insert does not touch the pre-state value is returned
unchanged. -/
theorem insert_tcb_rewrite_lookup {motive : TCB → TCB → Prop}
    (objs : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject)
    (nid k : SeLe4n.ObjId) (p q t0 : TCB)
    (hRefl : ∀ t : TCB, motive t t)
    (hInv : objs.invExt)
    (hRead : objs[nid]? = some (.tcb p))
    (hRel : motive q p)
    (hPre : objs[k]? = some (.tcb t0)) :
    ∃ t' : TCB, (objs.insert nid (.tcb q))[k]? = some (.tcb t')
      ∧ motive t' t0 := by
  by_cases hK : nid = k
  · -- The patched neighbour *is* `k`: the read value is `t0` (lookup
    -- determinism), and the rewrite bears `motive` to it by hypothesis.
    subst hK
    have hpt : p = t0 := by
      rw [hPre] at hRead
      injection hRead with h
      injection h with h
      exact h.symm
    subst hpt
    exact ⟨q, SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self _ _ _ hInv, hRel⟩
  · refine ⟨t0, ?_, hRefl t0⟩
    show (objs.insert nid (.tcb q)).get? k = some (.tcb t0)
    rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne _ _ _ _
      (fun hbeq => hK (eq_of_beq hbeq)) hInv]
    exact hPre

/-- WS-SM SM6.E: `spliceOutMidQueueNode` preserves TCB-kind at every key, and
what it leaves there is the value it read with **only its three intrusive queue
links** rewritten — which is what the link patches write.

**`v0.35.183` (register row 63)**: the conclusion was `cpuAffinity` agreement,
one consequence of the relation the branches actually establish.  The backward
reading (`spliceOutMidQueueNode_tcb_backward`) had concluded `tcbQueueLinkRewrite`
since WS-RR RR7.22; the forward one had not, so a frame over any *other* non-link
field — `schedContextBinding`, which `schedContextBindingConsistent` reads — could
not be stated without re-running this whole case analysis.  One relation, both
directions; `tcbQueueLinkRewrite.field` projects whichever field a frame needs. -/
theorem spliceOutMidQueueNode_tcb_lookup
    (st : SystemState) (tid : SeLe4n.ThreadId) (k : SeLe4n.ObjId) (t0 : TCB)
    (hInv : st.objects.invExt)
    (hPre : st.objects[k]? = some (.tcb t0)) :
    ∃ t' : TCB, (spliceOutMidQueueNode st tid).objects[k]? = some (.tcb t')
      ∧ tcbQueueLinkRewrite t' t0 := by
  simp only [spliceOutMidQueueNode]
  cases lookupTcb st tid with
  | none => exact ⟨t0, hPre, tcbQueueLinkRewrite.refl t0⟩
  | some tcb =>
    simp only []
    cases tcb.queuePrev with
    | none =>
      -- No predecessor patch: the successor patch acts on `st.objects`.
      simp only []
      cases tcb.queueNext with
      | none => exact ⟨t0, hPre, tcbQueueLinkRewrite.refl t0⟩
      | some nextTid =>
        simp only []
        cases hL2 : st.objects[nextTid.toObjId]? with
        | none => exact ⟨t0, hPre, tcbQueueLinkRewrite.refl t0⟩
        | some obj =>
          cases obj
          case tcb nextTcb =>
            exact insert_tcb_rewrite_lookup st.objects nextTid.toObjId k nextTcb
              (queueUnlinkSuccessor tcb nextTcb) t0 tcbQueueLinkRewrite.refl hInv hL2
              (tcbQueueLinkRewrite_queueUnlinkSuccessor tcb nextTcb) hPre
          all_goals exact ⟨t0, hPre, tcbQueueLinkRewrite.refl t0⟩
    | some prevTid =>
      simp only []
      cases hL : st.objects[prevTid.toObjId]? with
      | none =>
        -- Absent predecessor entry: successor patch over `st.objects`.
        simp only []
        cases tcb.queueNext with
        | none => exact ⟨t0, hPre, tcbQueueLinkRewrite.refl t0⟩
        | some nextTid =>
          simp only []
          cases hL2 : st.objects[nextTid.toObjId]? with
          | none => exact ⟨t0, hPre, tcbQueueLinkRewrite.refl t0⟩
          | some obj =>
            cases obj
            case tcb nextTcb =>
              exact insert_tcb_rewrite_lookup st.objects nextTid.toObjId k nextTcb
                (queueUnlinkSuccessor tcb nextTcb) t0 tcbQueueLinkRewrite.refl hInv hL2
                (tcbQueueLinkRewrite_queueUnlinkSuccessor tcb nextTcb) hPre
            all_goals exact ⟨t0, hPre, tcbQueueLinkRewrite.refl t0⟩
      | some obj =>
        cases obj
        case tcb prevTcb =>
          -- Predecessor patch applied: stage 2 acts on the patched table.
          simp only []
          cases tcb.queueNext with
          | none =>
            exact insert_tcb_rewrite_lookup st.objects prevTid.toObjId k prevTcb
              (queueUnlinkPredecessor tcb prevTcb) t0 tcbQueueLinkRewrite.refl hInv hL
              (tcbQueueLinkRewrite_queueUnlinkPredecessor tcb prevTcb) hPre
          | some nextTid =>
            simp only []
            have hInv1 : (st.objects.insert prevTid.toObjId
                (.tcb (queueUnlinkPredecessor tcb prevTcb))).invExt :=
              SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ hInv
            obtain ⟨t₁, hL1, hRw1⟩ :=
              insert_tcb_rewrite_lookup st.objects prevTid.toObjId k prevTcb
                (queueUnlinkPredecessor tcb prevTcb) t0 tcbQueueLinkRewrite.refl hInv hL
                (tcbQueueLinkRewrite_queueUnlinkPredecessor tcb prevTcb) hPre
            cases hL2 : (st.objects.insert prevTid.toObjId
                (.tcb (queueUnlinkPredecessor tcb prevTcb)))[nextTid.toObjId]? with
            | none => exact ⟨t₁, hL1, hRw1⟩
            | some obj2 =>
              cases obj2
              case tcb nextTcb =>
                obtain ⟨t₂, hL2', hRw2⟩ :=
                  insert_tcb_rewrite_lookup
                    (st.objects.insert prevTid.toObjId
                      (.tcb (queueUnlinkPredecessor tcb prevTcb)))
                    nextTid.toObjId k nextTcb
                    (queueUnlinkSuccessor tcb nextTcb) t₁ tcbQueueLinkRewrite.refl hInv1 hL2
                    (tcbQueueLinkRewrite_queueUnlinkSuccessor tcb nextTcb) hL1
                exact ⟨t₂, hL2', hRw2.trans hRw1⟩
              all_goals exact ⟨t₁, hL1, hRw1⟩
        all_goals
          -- Non-TCB predecessor entry: successor patch over `st.objects`.
          (simp only []
           cases tcb.queueNext with
           | none => exact ⟨t0, hPre, tcbQueueLinkRewrite.refl t0⟩
           | some nextTid =>
             simp only []
             cases hL2 : st.objects[nextTid.toObjId]? with
             | none => exact ⟨t0, hPre, tcbQueueLinkRewrite.refl t0⟩
             | some obj2 =>
               cases obj2
               case tcb nextTcb =>
                 exact insert_tcb_rewrite_lookup st.objects nextTid.toObjId k nextTcb
                   (queueUnlinkSuccessor tcb nextTcb) t0 tcbQueueLinkRewrite.refl hInv hL2
                   (tcbQueueLinkRewrite_queueUnlinkSuccessor tcb nextTcb) hPre
               all_goals exact ⟨t0, hPre, tcbQueueLinkRewrite.refl t0⟩)

/-- WS-SM SM6.E: the endpoint sweep preserves TCB-kind and `TCB.placement` (home core and
run-queue links) at every key (and `objects.invExt`) — every fold step rewrites an
`.endpoint`-valued key, which can never alias a TCB-holding key (the fold
keystone `RHTable.fold_preserves_of_lookup` supplies the visited key's
stored value, so the kind clash discharges the disequality). -/
theorem removeFromAllEndpointQueues_tcb_lookup
    (st : SystemState) (tid : SeLe4n.ThreadId) (k : SeLe4n.ObjId) (t0 : TCB)
    (hInv : st.objects.invExt)
    (hPre : st.objects[k]? = some (.tcb t0)) :
    (removeFromAllEndpointQueues st tid).objects.invExt
    ∧ ∃ t' : TCB,
      (removeFromAllEndpointQueues st tid).objects[k]? = some (.tcb t')
      ∧ t'.placement = t0.placement := by
  obtain ⟨t₁, hL1, hRw1⟩ := spliceOutMidQueueNode_tcb_lookup st tid k t0 hInv hPre
  have hAff1 : t₁.placement = t0.placement :=
    hRw1.field TCB.placement (fun _ _ _ _ _ _ => rfl)
  have hInvS := spliceOutMidQueueNode_preserves_objects_invExt st tid hInv
  unfold removeFromAllEndpointQueues
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves_of_lookup
    (spliceOutMidQueueNode st tid).objects (spliceOutMidQueueNode st tid) _
    (fun acc => acc.objects.invExt ∧ ∃ t' : TCB,
      acc.objects[k]? = some (.tcb t') ∧ t'.placement = t0.placement)
    hInvS
    ⟨hInvS, t₁, hL1, hAff1⟩
    (fun acc x v hV hAcc => by
      obtain ⟨hAccInv, t', hL', hAff'⟩ := hAcc
      split
      · -- `.endpoint` step: the visited key holds an endpoint, so it cannot
        -- be `k` (which holds a TCB in the fold source by `hL1`).  The
        -- write-set-honest sweep only inserts when the victim touches the
        -- endpoint's head/tail slots (PR #831 review 4); the untouched arm
        -- is the identity.
        split
        · split
          · have hNe : x ≠ k := fun hxk => by
              subst hxk
              have hclash := hL1.symm.trans hV
              injection hclash with h
              injection h
            exact ⟨SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hAccInv,
              t',
              (SystemState.rewriteObject_objects_ne _ _ _ _ _ hNe hAccInv).trans hL',
              hAff'⟩
          · exact ⟨hAccInv, t', hL', hAff'⟩
        · exact ⟨hAccInv, t', hL', hAff'⟩
      · exact ⟨hAccInv, t', hL', hAff'⟩)

/-- WS-ZA ZA4.4: a TCB before the unlink is a TCB after it, with at most its
intrusive links rewritten. -/
theorem removeFromNotificationWaitQueue_tcb_forward
    (st : SystemState) (tid : SeLe4n.ThreadId) (k : SeLe4n.ObjId) (t0 : TCB)
    (hInv : st.objects.invExt)
    (hPre : st.objects[k]? = some (.tcb t0)) :
    ∃ t' : TCB, (removeFromNotificationWaitQueue st tid).objects[k]? = some (.tcb t')
      ∧ tcbNtfnLinkRewrite t' t0 := by
  rcases (removeFromNotificationWaitQueue_reach st tid hInv).2 k with
    h | ⟨n, _, hn, _, _, _, _⟩ | ⟨t, t', ht, ht', hR⟩
  · exact ⟨t0, h.trans hPre, tcbNtfnLinkRewrite.refl t0⟩
  · rw [hPre] at hn; cases hn
  · rw [hPre] at ht; cases ht; exact ⟨t', ht', hR⟩

/-- WS-ZA ZA4.4: and a TCB after the unlink was one before it. -/
theorem removeFromNotificationWaitQueue_tcb_backward
    (st : SystemState) (tid : SeLe4n.ThreadId) (k : SeLe4n.ObjId) (t' : TCB)
    (hInv : st.objects.invExt)
    (hPost : (removeFromNotificationWaitQueue st tid).objects[k]? = some (.tcb t')) :
    ∃ t0 : TCB, st.objects[k]? = some (.tcb t0) ∧ tcbNtfnLinkRewrite t' t0 := by
  rcases (removeFromNotificationWaitQueue_reach st tid hInv).2 k with
    h | ⟨n, n', _, hn', _, _, _⟩ | ⟨t, t2, ht, ht', hR⟩
  · exact ⟨t', h ▸ hPost, tcbNtfnLinkRewrite.refl t'⟩
  · rw [hPost] at hn'; cases hn'
  · rw [hPost] at ht'; cases ht'; exact ⟨t, ht, hR⟩

/-- WS-ZA ZA4.4: a slot holding neither a notification nor a TCB is untouched. -/
theorem removeFromNotificationWaitQueue_other_slot
    (st : SystemState) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (k : SeLe4n.ObjId) (o : KernelObject) (hNotN : ∀ n, o ≠ .notification n)
    (hNotT : ∀ t, o ≠ .tcb t) :
    (removeFromNotificationWaitQueue st tid).objects[k]? = some o ↔
      st.objects[k]? = some o := by
  rcases (removeFromNotificationWaitQueue_reach st tid hInv).2 k with
    h | ⟨n, n', hn, hn', _, _, _⟩ | ⟨t, t2, ht, ht', _⟩
  · rw [h]
  · rw [hn, hn']
    exact ⟨fun h => absurd (Option.some.inj h).symm (hNotN n'),
      fun h => absurd (Option.some.inj h).symm (hNotN n)⟩
  · rw [ht, ht']
    exact ⟨fun h => absurd (Option.some.inj h).symm (hNotT t2),
      fun h => absurd (Option.some.inj h).symm (hNotT t)⟩

/-- WS-ZA ZA4.4: every TCB field the intrusive links do not carry reads the same
through `getTcb?` after the unlink. -/
theorem removeFromNotificationWaitQueue_tcbField_frame {α : Type} (f : TCB → α)
    (hf : ∀ (t : TCB) qp qpp qn np nn,
      f { t with
        queuePrevCode := qp, queuePPrevCode := qpp, queueNextCode := qn,
        ntfnPrevCode := np, ntfnNextCode := nn } = f t)
    (st : SystemState) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (x : SeLe4n.ThreadId) :
    ((removeFromNotificationWaitQueue st tid).getTcb? x).map f = (st.getTcb? x).map f := by
  refine SystemState.map_tcbField_eq_of_refines f (fun t0 hT0 => ?_) (fun t' hT' => ?_)
  · obtain ⟨t', hL', hRw'⟩ := removeFromNotificationWaitQueue_tcb_forward st tid x.toObjId t0
      hInv ((SystemState.getTcb?_eq_some_iff st x t0).mp hT0)
    exact ⟨t', (SystemState.getTcb?_eq_some_iff _ x t').mpr hL', hRw'.toQueueLinkRewrite.field f hf⟩
  · obtain ⟨t0, hL0, _⟩ := removeFromNotificationWaitQueue_tcb_backward st tid x.toObjId t'
      hInv ((SystemState.getTcb?_eq_some_iff _ x t').mp hT')
    exact ⟨t0, (SystemState.getTcb?_eq_some_iff st x t0).mpr hL0⟩

/-- WS-SM SM6.E: the notification unlink preserves TCB-kind and `TCB.placement`
(home core and run-queue links) at every key (and `objects.invExt`). -/
theorem removeFromNotificationWaitQueue_tcb_lookup
    (st : SystemState) (tid : SeLe4n.ThreadId) (k : SeLe4n.ObjId) (t0 : TCB)
    (hInv : st.objects.invExt)
    (hPre : st.objects[k]? = some (.tcb t0)) :
    (removeFromNotificationWaitQueue st tid).objects.invExt
    ∧ ∃ t' : TCB,
      (removeFromNotificationWaitQueue st tid).objects[k]? = some (.tcb t')
      ∧ t'.placement = t0.placement := by
  obtain ⟨t', h, hR⟩ := removeFromNotificationWaitQueue_tcb_forward st tid k t0 hInv hPre
  exact ⟨(removeFromNotificationWaitQueue_reach st tid hInv).1, t', h,
    hR.toQueueLinkRewrite.field TCB.placement (fun _ _ _ _ _ _ => rfl)⟩

/-- WS-SM SM6.E: a thread id whose key holds no TCB resolves to `none` under
`lookupTcb` — both the reserved-id guard and the kind-mismatch arm return
`none`. -/
theorem lookupTcb_eq_none_of_no_tcb
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hNo : ∀ t : TCB, st.objects[tid.toObjId]? ≠ some (.tcb t)) :
    lookupTcb st tid = none := by
  unfold lookupTcb SystemState.getTcb?
  split
  · rfl
  · split
    · rename_i t heq
      exact absurd heq (hNo t)
    · rfl

/-- WS-SM SM6.E: the mid-queue splice is the identity when the spliced thread
resolves to no TCB — the link patches are guarded on the victim's TCB read. -/
theorem spliceOutMidQueueNode_eq_self_of_lookupTcb_none
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (h : lookupTcb st tid = none) :
    spliceOutMidQueueNode st tid = st := by
  unfold spliceOutMidQueueNode
  rw [h]

/-- WS-SM SM6.E: the endpoint sweep never materialises a TCB at the swept
thread's key — when the key holds no TCB before the sweep, it holds no TCB
afterwards (the splice is guarded to the identity and every fold step writes
an `.endpoint` value). -/
theorem removeFromAllEndpointQueues_no_tcb
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt)
    (hNo : ∀ t : TCB, st.objects[tid.toObjId]? ≠ some (.tcb t)) :
    (removeFromAllEndpointQueues st tid).objects.invExt
    ∧ ∀ t : TCB,
      (removeFromAllEndpointQueues st tid).objects[tid.toObjId]? ≠ some (.tcb t) := by
  have hSplice : spliceOutMidQueueNode st tid = st :=
    spliceOutMidQueueNode_eq_self_of_lookupTcb_none st tid
      (lookupTcb_eq_none_of_no_tcb st tid hNo)
  unfold removeFromAllEndpointQueues
  rw [hSplice]
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves_of_lookup st.objects st _
    (fun acc => acc.objects.invExt ∧ ∀ t : TCB,
      acc.objects[tid.toObjId]? ≠ some (.tcb t))
    hInv
    ⟨hInv, hNo⟩
    (fun acc x v _ hAcc => by
      obtain ⟨hAccInv, hNoT⟩ := hAcc
      split
      · -- write-set-honest sweep (PR #831 review 4): the insert arm is
        -- guarded; the untouched arm is the identity.
        split
        · split
          · refine ⟨SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hAccInv,
              fun t h => ?_⟩
            by_cases hx : x = tid.toObjId
            · -- The swept key itself is rewritten in its own kind — not to a TCB.
              subst hx
              have hclash := (SystemState.rewriteObject_objects_self
                acc tid.toObjId _ _ hAccInv).symm.trans h
              injection hclash with hclash
              injection hclash
            · exact hNoT t ((SystemState.rewriteObject_objects_ne
                acc x tid.toObjId _ _ hx hAccInv).symm.trans h)
          · exact ⟨hAccInv, hNoT⟩
        · exact ⟨hAccInv, hNoT⟩
      · exact ⟨hAccInv, hNoT⟩)

/-- WS-SM SM6.E: the notification unlink never materialises a TCB at a key
that held none — its TCB writes are in-place link rewrites. -/
theorem removeFromNotificationWaitQueue_no_tcb
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt)
    (hNo : ∀ t : TCB, st.objects[tid.toObjId]? ≠ some (.tcb t)) :
    (removeFromNotificationWaitQueue st tid).objects.invExt
    ∧ ∀ t : TCB,
      (removeFromNotificationWaitQueue st tid).objects[tid.toObjId]?
        ≠ some (.tcb t) := by
  refine ⟨(removeFromNotificationWaitQueue_reach st tid hInv).1, fun t h => ?_⟩
  obtain ⟨t0, h0, _⟩ := removeFromNotificationWaitQueue_tcb_backward st tid _ t hInv h
  exact hNo t0 h0

-- ============================================================================
-- WS-SM SM6.E: cleanup primitives preserve `ipcInvariant`
-- ============================================================================
-- The notification well-formedness invariant (`ipcInvariant`) across the
-- cancellation sweeps: the splice and the endpoint sweep write only
-- `.tcb`/`.endpoint` values (which can never be read back as a
-- notification), and the notification sweep's filter+state-correction
-- rewrite preserves the three-case well-formedness by construction.

/-- WS-SM SM6.E: a notification read through a non-notification insert was
already present in the base table — the table-level backward transport every
non-notification write in the cancellation path instantiates. -/
theorem notification_lookup_of_insert_no_notification
    (objs : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject)
    (nid : SeLe4n.ObjId) (v : KernelObject)
    (hInv : objs.invExt)
    (hV : ∀ n : Notification, v ≠ .notification n)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hL : (objs.insert nid v)[oid]? = some (.notification ntfn)) :
    objs[oid]? = some (.notification ntfn) := by
  by_cases hx : (nid == oid) = true
  · have hk : nid = oid := eq_of_beq hx
    subst hk
    have hclash := (SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self
      objs nid v hInv).symm.trans hL
    injection hclash with hclash
    exact absurd hclash (hV ntfn)
  · exact (SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne
      objs nid oid v hx hInv).symm.trans hL

/-- WS-SM SM6.E: inserting a non-notification value preserves `ipcInvariant`
— a notification read in the post-store either hits the inserted key (kind
clash, vacuous) or was already present. -/
theorem ipcInvariant_insert_no_notification
    (st : SystemState) (nid : SeLe4n.ObjId) (v : KernelObject)
    (hInv : st.objects.invExt)
    (hV : ∀ n : Notification, v ≠ .notification n)
    (hIpc : ipcInvariant st) :
    ipcInvariant { st with objects := st.objects.insert nid v } := by
  intro oid ntfn hL
  exact hIpc oid ntfn
    (notification_lookup_of_insert_no_notification st.objects nid v hInv hV oid ntfn hL)

/-- WS-SM SM6.E: `.tcb`-insert instance of
`ipcInvariant_insert_no_notification` (ctor-headed for robust inference). -/
theorem ipcInvariant_insert_tcb
    (st : SystemState) (nid : SeLe4n.ObjId) (t : TCB)
    (hInv : st.objects.invExt) (hIpc : ipcInvariant st) :
    ipcInvariant { st with objects := st.objects.insert nid (.tcb t) } :=
  ipcInvariant_insert_no_notification st nid (.tcb t) hInv
    (fun _ h => KernelObject.noConfusion h) hIpc

/-- WS-SM SM6.E: `.endpoint`-insert instance of
`ipcInvariant_insert_no_notification`. -/
theorem ipcInvariant_insert_endpoint
    (st : SystemState) (nid : SeLe4n.ObjId) (e : Endpoint)
    (hInv : st.objects.invExt) (hIpc : ipcInvariant st) :
    ipcInvariant { st with objects := st.objects.insert nid (.endpoint e) } :=
  ipcInvariant_insert_no_notification st nid (.endpoint e) hInv
    (fun _ h => KernelObject.noConfusion h) hIpc

/-- WS-SM SM6.E: `spliceOutMidQueueNode` preserves `ipcInvariant` — both link
patches write `.tcb` values, never a notification. -/
theorem spliceOutMidQueueNode_preserves_ipcInvariant
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hIpc : ipcInvariant st) :
    ipcInvariant (spliceOutMidQueueNode st tid) := by
  simp only [spliceOutMidQueueNode]
  cases lookupTcb st tid with
  | none => exact hIpc
  | some tcb =>
    simp only []
    cases tcb.queuePrev with
    | none =>
      simp only []
      cases tcb.queueNext with
      | none => exact hIpc
      | some nextTid =>
        simp only []
        cases st.objects[nextTid.toObjId]? with
        | none => exact hIpc
        | some obj =>
          cases obj
          case tcb nextTcb => exact ipcInvariant_insert_tcb st nextTid.toObjId _ hInv hIpc
          all_goals exact hIpc
    | some prevTid =>
      simp only []
      cases st.objects[prevTid.toObjId]? with
      | none =>
        simp only []
        cases tcb.queueNext with
        | none => exact hIpc
        | some nextTid =>
          simp only []
          cases st.objects[nextTid.toObjId]? with
          | none => exact hIpc
          | some obj =>
            cases obj
            case tcb nextTcb =>
              exact ipcInvariant_insert_tcb st nextTid.toObjId _ hInv hIpc
            all_goals exact hIpc
      | some obj =>
        cases obj
        case tcb prevTcb =>
          simp only []
          cases tcb.queueNext with
          | none => exact ipcInvariant_insert_tcb st prevTid.toObjId _ hInv hIpc
          | some nextTid =>
            simp only []
            have hInv1 : (st.objects.insert prevTid.toObjId
                (.tcb (queueUnlinkPredecessor tcb prevTcb))).invExt :=
              SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ hInv
            have hIpc1 : ipcInvariant { st with
                objects := st.objects.insert prevTid.toObjId
                  (.tcb (queueUnlinkPredecessor tcb prevTcb)) } :=
              ipcInvariant_insert_tcb st prevTid.toObjId _ hInv hIpc
            cases (st.objects.insert prevTid.toObjId
                (.tcb (queueUnlinkPredecessor tcb prevTcb)))[nextTid.toObjId]? with
            | none => exact hIpc1
            | some obj2 =>
              cases obj2
              case tcb nextTcb =>
                exact ipcInvariant_insert_tcb
                  { st with
                      objects := st.objects.insert prevTid.toObjId
                        (.tcb (queueUnlinkPredecessor tcb prevTcb)) }
                  nextTid.toObjId _ hInv1 hIpc1
              all_goals exact hIpc1
        all_goals
          (simp only []
           cases tcb.queueNext with
           | none => exact hIpc
           | some nextTid =>
             simp only []
             cases st.objects[nextTid.toObjId]? with
             | none => exact hIpc
             | some obj2 =>
               cases obj2
               case tcb nextTcb =>
                 exact ipcInvariant_insert_tcb st nextTid.toObjId _ hInv hIpc
               all_goals exact hIpc)

/-- WS-SM SM6.E: the endpoint sweep preserves `ipcInvariant` — the splice
writes `.tcb` values and every fold step writes an `.endpoint` value. -/
theorem removeFromAllEndpointQueues_preserves_ipcInvariant
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hIpc : ipcInvariant st) :
    ipcInvariant (removeFromAllEndpointQueues st tid) := by
  have hInvS := spliceOutMidQueueNode_preserves_objects_invExt st tid hInv
  have hIpcS := spliceOutMidQueueNode_preserves_ipcInvariant st tid hInv hIpc
  unfold removeFromAllEndpointQueues
  exact (SeLe4n.Kernel.RobinHood.RHTable.fold_preserves
    (spliceOutMidQueueNode st tid).objects (spliceOutMidQueueNode st tid) _
    (fun acc => acc.objects.invExt ∧ ipcInvariant acc)
    ⟨hInvS, hIpcS⟩
    (fun acc _ _ hAcc => by
      split
      · split
        · split
          · exact ⟨SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hAcc.1,
              ipcInvariant_insert_endpoint acc _ _ hAcc.1 hAcc.2⟩
          · exact hAcc
        · exact hAcc
      · exact hAcc)).2

/-- WS-SM SM6.E: the notification unlink preserves `ipcInvariant` — its one
notification rewrite is well formed from the source's
(`notificationQueueWellFormed_unlink`), and its TCB writes touch no
notification. -/
theorem removeFromNotificationWaitQueue_preserves_ipcInvariant
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hIpc : ipcInvariant st) :
    ipcInvariant (removeFromNotificationWaitQueue st tid) := by
  intro oid ntfn hL
  rcases (removeFromNotificationWaitQueue_reach st tid hInv).2 oid with
    h | ⟨n, n', hn, hn', _, _, hW⟩ | ⟨t, t', _, ht', _⟩
  · exact hIpc oid ntfn (h ▸ hL)
  · rw [hL] at hn'; cases hn'; exact hW (hIpc oid n hn)
  · rw [hL] at ht'; cases ht'

/-- WS-SM SM6.E: `cleanupDonatedSchedContext` preserves `objects.invExt` —
the identity arms are trivial and the `.donated` arm delegates to
`returnDonatedSchedContext` (three `storeObject` steps, AI4-A). -/
theorem cleanupDonatedSchedContext_preserves_objects_invExt
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt)
    (h : cleanupDonatedSchedContext st tid = .ok st') :
    st'.objects.invExt := by
  unfold cleanupDonatedSchedContext at h
  split at h
  · -- lookupTcb = none: identity.
    injection h with h; subst h; exact hInv
  · split at h
    · -- `.donated scId originalOwner`: delegate to returnDonatedSchedContext.
      exact returnDonatedSchedContextResolved_lift h
        (fun n s hs => returnDonatedSchedContext_preserves_objects_invExt _ _ _ _ _ hInv n hs)
    · -- `.bound` / `.unbound`: identity.
      injection h with h; subst h; exact hInv

/-- WS-SM SM6.E: `cleanupDonatedSchedContext` preserves `ipcInvariant` — the
identity arms are trivial and the `.donated` arm's three `storeObject` steps
write a SchedContext and two TCBs, never a notification
(`returnDonatedSchedContext_notification_backward`). -/
theorem cleanupDonatedSchedContext_preserves_ipcInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hIpc : ipcInvariant st)
    (h : cleanupDonatedSchedContext st tid = .ok st') :
    ipcInvariant st' := by
  unfold cleanupDonatedSchedContext at h
  split at h
  · injection h with h; subst h; exact hIpc
  · split at h
    · obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose h
      intro oid ntfn hL
      exact hIpc oid ntfn
        (returnDonatedSchedContext_notification_backward _ _ _ _ _ hInv n hPop oid ntfn hL)
    · injection h with h; subst h; exact hIpc

-- ============================================================================
-- `v0.35.164`: the per-core donation-cancellation arms' frames
-- ============================================================================
--
-- The four WS-SM SM6.E.3 frames below moved here from
-- `IPC/CrossCore/Cancellation.lean` with the definitions they are about (see the
-- section note above `cancelBoundDonationOnCore` in `Cleanup.lean`): the destroy
-- path's proofs read them, and that layer sits above this module.  The
-- `_machine_eq` / `_tlbShootdown_eq` pair on each arm and the dispatcher's own
-- four are new — they are exactly what `lifecyclePreRetypeCleanup`'s theorems
-- read of the pipeline's first step.

/-- WS-SM SM6.E.3: `cancelBoundDonationOnCore` preserves `objects.invExt` —
the per-core replenish-queue purge does not touch `objects`; the object
writes are the same SchedContext deactivation and TCB unbind inserts as the
single-core arm. -/
theorem cancelBoundDonationOnCore_preserves_objects_invExt
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt)
    (h : cancelBoundDonationOnCore st tid tcb = .ok st') :
    st'.objects.invExt := by
  unfold cancelBoundDonationOnCore at h
  split at h
  · injection h with h
    subst h
    rw [markKeyChangeFrom_objects]
    exact SystemState.updateTcb_preserves_objects_invExt _ _ _
      (SchedContextOps.purgeReplenishment_objects_invExt _ _
        (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv))
  · cases h

/-- WS-SM SM6.E.3: the bound arm's purge edits only the release queues —
every core's run queue and current slot are exactly the pre-state's (the
donation cancellation wakes and deschedules nothing). -/
theorem cancelBoundDonationOnCore_runQueue_current_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (c : SeLe4n.Kernel.Concurrency.CoreId)
    (h : cancelBoundDonationOnCore st tid tcb = .ok st') :
    st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c
    ∧ st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c := by
  simp only [cancelBoundDonationOnCore] at h
  split at h
  · injection h with h
    subst h
    rw [markKeyChangeFrom_runQueueOnCore, markKeyChangeFrom_currentOnCore]
    constructor <;>
      (rw [SystemState.updateTcb_scheduler]
       simp [SystemState.updateSchedContext_scheduler])
  · cases h

/-- WS-SM SM6.E.3 / WS-ZA ZA6.3 (the purge, positively): on the `.bound scId`
arm every entry left on any core's queue was there before, and one naming the
SchedContext survives only on a core its own link did not name — the queue that
link names is purged exactly, and nothing else is. -/
theorem cancelBoundDonationOnCore_replenishQueue_purged
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (scId : SeLe4n.SchedContextId)
    (hBind : tcb.schedContextBinding = .bound scId)
    (hInv : st.objects.invExt)
    (h : cancelBoundDonationOnCore st tid tcb = .ok st')
    (c : SeLe4n.Kernel.Concurrency.CoreId) (e : SeLe4n.SchedContextId × Nat)
    (he : e ∈ (st'.scheduler.replenishQueueOnCore c).entries) :
    e ∈ (st.scheduler.replenishQueueOnCore c).entries ∧
      (e.1 = scId → st.releaseCoreOf scId ≠ some c) := by
  simp only [cancelBoundDonationOnCore, hBind] at h
  injection h with h
  subst h
  rw [markKeyChangeFrom_replenishQueueOnCore, SystemState.updateTcb_scheduler] at he
  refine ⟨?_, fun hs => ?_⟩
  · have := SchedContextOps.purgeReplenishment_entries_subset _ scId c e he
    rwa [SystemState.updateSchedContext_scheduler] at this
  · rw [← SystemState.releaseCoreOf_updateSchedContext st scId
      (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })
      hInv (fun _ => rfl) scId]
    exact SchedContextOps.purgeReplenishment_entries_self _ scId c e he hs

/-- …and over agreeing queues, none naming the SchedContext survives anywhere. -/
theorem cancelBoundDonationOnCore_replenishQueue_purged_of_refined
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (scId : SeLe4n.SchedContextId)
    (hBind : tcb.schedContextBinding = .bound scId)
    (hInv : st.objects.invExt) (hRef : st.releaseQueueRefined)
    (h : cancelBoundDonationOnCore st tid tcb = .ok st')
    (c : SeLe4n.Kernel.Concurrency.CoreId) (e : SeLe4n.SchedContextId × Nat)
    (he : e ∈ (st'.scheduler.replenishQueueOnCore c).entries) :
    e ∈ (st.scheduler.replenishQueueOnCore c).entries ∧ e.1 ≠ scId := by
  obtain ⟨hm, hs⟩ := cancelBoundDonationOnCore_replenishQueue_purged st st' tid tcb scId
    hBind hInv h c e he
  refine ⟨hm, fun hEq => hs hEq (SystemState.releaseCoreOf_of_queuedOn ?_)⟩
  refine ((hRef c).queued scId).mpr ?_
  exact List.mem_map.mpr ⟨e, hm, hEq⟩

/-- WS-ZA ZA6.3: the unbind keeps every core's release queue agreeing with the
contexts' links — the context write keeps its release fields, the purge unlinks
it through its neighbours, and the binding clear and key hook write none. -/
theorem cancelBoundDonationOnCore_refined {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB}
    (hInv : st.objects.invExt) (hRef : st.releaseQueueRefined)
    (h : cancelBoundDonationOnCore st tid tcb = .ok st') : st'.releaseQueueRefined := by
  unfold cancelBoundDonationOnCore at h
  split at h
  · rename_i scId _
    cases h
    have hMid := SystemState.updateSchedContext_preserves_objects_invExt st scId
      (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) hInv
    have h1 := (SystemState.releaseStateAgree.updateSchedContext st scId
      (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) hInv
      (fun _ => ⟨rfl, rfl, rfl⟩)).refined hRef
    have h2 := SchedContextOps.purgeReplenishment_refined h1 scId
    have hX := SchedContextOps.purgeReplenishment_objects_invExt _ scId hMid
    have h3 := (SystemState.releaseStateAgree.of_getSchedContext?
      (SystemState.updateTcb_getSchedContext? _ tid
        (fun tcb' => { tcb' with scBindingScCode := 0, scBindingOwnerCode := 0 }) hX)
      (by rw [SystemState.updateTcb_scheduler])).refined h2
    exact (SystemState.releaseStateAgree.of_objects_eq (markKeyChangeFrom_objects _ _ _)
      (markKeyChangeFrom_releaseSlots _ _ _)).refined h3
  · cases h

/-- `v0.35.164`: the bound arm writes no register bank — two object rewrites and
two record updates, none of which names `machine`. -/
theorem cancelBoundDonationOnCore_machine_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : cancelBoundDonationOnCore st tid tcb = .ok st') :
    st'.machine = st.machine := by
  simp only [cancelBoundDonationOnCore] at h
  split at h
  · injection h with h
    subst h
    rw [markKeyChangeFrom_machine, SystemState.updateTcb_eq_objects_update]
    show (SchedContextOps.purgeReplenishment _ _).machine = _
    rw [SchedContextOps.purgeReplenishment_machine, SystemState.updateSchedContext_eq_objects_update]
  · cases h

/-- `v0.35.164`: ...nor the TLB-shootdown state, for the same reason. -/
theorem cancelBoundDonationOnCore_tlbShootdown_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : cancelBoundDonationOnCore st tid tcb = .ok st') :
    st'.tlbShootdown = st.tlbShootdown := by
  simp only [cancelBoundDonationOnCore] at h
  split at h
  · injection h with h
    subst h
    rw [markKeyChangeFrom_tlbShootdown, SystemState.updateTcb_eq_objects_update]
    show (SchedContextOps.purgeReplenishment _ _).tlbShootdown = _
    rw [SchedContextOps.purgeReplenishment_tlbShootdown, SystemState.updateSchedContext_eq_objects_update]
  · cases h

/-- WS-SM SM6.E.3: the per-core donated arm preserves `objects.invExt` — the
return preserves it and the migration never touches `objects`. -/
theorem cancelDonatedDonationOnCore_preserves_objects_invExt
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st') :
    st'.objects.invExt := by
  unfold cancelDonatedDonationOnCore at h
  split at h
  · -- `.donated` arm.
    split at h
    · cases h
    · injection h with h
      subst h
      exact migrateSchedContextReplenishment_preserves_objects_invExt _ _ _ _
        (cleanupDonatedSchedContext_preserves_objects_invExt _ _ _ hInv (by assumption))
  · cases h

/-- WS-SM SM6.E.3: the per-core donated arm never disturbs any core's run
queue or current slot (return: object writes only; migration: replenish
slots only). -/
theorem cancelDonatedDonationOnCore_runQueue_current_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (c : SeLe4n.Kernel.Concurrency.CoreId)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st') :
    st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c
    ∧ st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c := by
  unfold cancelDonatedDonationOnCore at h
  split at h
  · split at h
    · cases h
    · injection h with h
      subst h
      rename_i st1 hClean
      have hS := cleanupDonatedSchedContext_scheduler_eq st st1 tid hClean
      obtain ⟨hRQ, hCur⟩ := migrateSchedContextReplenishment_runQueue_current_eq
        st1 _ (determineTargetCore st tid) _ c
      constructor
      · rw [hRQ, hS]; rfl
      · rw [hCur, hS]; rfl
  · cases h

/-- `v0.35.164`: the donated arm writes no register bank — the return does not
(`cleanupDonatedSchedContext_machine_eq`) and the migration writes only two
replenish-queue slots. -/
theorem cancelDonatedDonationOnCore_machine_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st') :
    st'.machine = st.machine := by
  unfold cancelDonatedDonationOnCore at h
  split at h
  · split at h
    · cases h
    · injection h with h
      subst h
      rename_i st1 hClean
      rw [migrateSchedContextReplenishment_machine]
      exact cleanupDonatedSchedContext_machine_eq st st1 tid hClean
  · cases h

/-- `v0.35.164`: ...nor the TLB-shootdown state. -/
theorem cancelDonatedDonationOnCore_tlbShootdown_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st') :
    st'.tlbShootdown = st.tlbShootdown := by
  unfold cancelDonatedDonationOnCore at h
  split at h
  · split at h
    · cases h
    · injection h with h
      subst h
      rename_i st1 hClean
      rw [migrateSchedContextReplenishment_tlbShootdown]
      exact cleanupDonatedSchedContext_tlbShootdown_eq st st1 tid hClean
  · cases h

/-- `v0.35.164`: the dispatcher preserves `objects.invExt` on every arm. -/
theorem cancelDonationArmOnCore_preserves_objects_invExt
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt)
    (h : cancelDonationArmOnCore st tid tcb = .ok st') :
    st'.objects.invExt := by
  unfold cancelDonationArmOnCore at h
  split at h
  · injection h with h; subst h; exact hInv
  · exact cancelBoundDonationOnCore_preserves_objects_invExt _ _ _ _ hInv h
  · exact cancelDonatedDonationOnCore_preserves_objects_invExt _ _ _ _ hInv h

/-- `v0.35.164`: the dispatcher never disturbs any core's run queue or current
slot — it may purge or migrate a **replenish** queue, and that is all the
scheduler it writes.  What the destroy path's pipeline theorems read of its
first step, and what lets the retype's write set be read at the pipeline's
entry state (`lifecyclePreRetypeCleanup_confinedToCores`). -/
theorem cancelDonationArmOnCore_runQueue_current_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (c : SeLe4n.Kernel.Concurrency.CoreId)
    (h : cancelDonationArmOnCore st tid tcb = .ok st') :
    st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c
    ∧ st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c := by
  unfold cancelDonationArmOnCore at h
  split at h
  · injection h with h; subst h; exact ⟨rfl, rfl⟩
  · exact cancelBoundDonationOnCore_runQueue_current_eq _ _ _ _ c h
  · exact cancelDonatedDonationOnCore_runQueue_current_eq _ _ _ _ c h

/-- `v0.35.164`: the dispatcher writes no register bank. -/
theorem cancelDonationArmOnCore_machine_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : cancelDonationArmOnCore st tid tcb = .ok st') :
    st'.machine = st.machine := by
  unfold cancelDonationArmOnCore at h
  split at h
  · injection h with h; subst h; rfl
  · exact cancelBoundDonationOnCore_machine_eq _ _ _ _ h
  · exact cancelDonatedDonationOnCore_machine_eq _ _ _ _ h

/-- `v0.35.164`: the dispatcher never touches the TLB-shootdown state. -/
theorem cancelDonationArmOnCore_tlbShootdown_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : cancelDonationArmOnCore st tid tcb = .ok st') :
    st'.tlbShootdown = st.tlbShootdown := by
  unfold cancelDonationArmOnCore at h
  split at h
  · injection h with h; subst h; rfl
  · exact cancelBoundDonationOnCore_tlbShootdown_eq _ _ _ _ h
  · exact cancelDonatedDonationOnCore_tlbShootdown_eq _ _ _ _ h

-- ----------------------------------------------------------------------------
-- `v0.35.164`: the arm leaves the replenish queues where the bound threads are
-- ----------------------------------------------------------------------------
--
-- Neither per-core arm carried `replenishQueueAffinityConsistent_smp` before
-- this version.  The suspend pipeline had run both since WS-SM SM6.E.3 with the
-- invariant stated of its G2 teardown
-- (`cancelIpcBlockingMigrated_establishes_replenishQueueAffinityConsistent_smp`)
-- and of nothing after it, so the theorem the destroy path inherits here is
-- also the one the suspend's own G3 was owed.  Stated once, at the arm, for
-- both callers -- and, for the `.donated` arm, through the general
-- `migrateSchedContextReplenishment_to_home_preserves_affinityConsistent_smp`
-- that `v0.35.161`'s pre-receive return composes, so the migration's
-- destination obligation has one owner rather than a copy per hand-off.

/-- `v0.35.164`: a successful in-place unbind witnesses the `.bound` binding it
matched on. -/
theorem cancelBoundDonationOnCore_ok_bound
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : cancelBoundDonationOnCore st tid tcb = .ok st') :
    ∃ scId, tcb.schedContextBinding = .bound scId := by
  unfold cancelBoundDonationOnCore at h
  split at h
  · rename_i scId hBind; exact ⟨scId, hBind⟩
  · cases h

/-- The read frame of the shape the in-place unbind writes: a SchedContext slot
rewritten through `g`, then -- after any scheduler or index edit, which `hs`
leaves free -- a TCB slot rewritten `cpuAffinity`-preserving.  Every other
SchedContext resolves as before, the rewritten one reads back through `g`, and
every thread keeps its home core.  Stated over an intermediate state `s` fixed
only by its object table, because the arm's intermediate state is a record
update chain whose spelling no consumer should have to reproduce. -/
private theorem scUpdate_then_tcbUpdate_read_frame
    (st s : SystemState) (scId : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) (tid : SeLe4n.ThreadId) (f : TCB → TCB)
    (hf : ∀ t, (f t).cpuAffinity = t.cpuAffinity)
    (hInv : st.objects.invExt) (hsInv : s.objects.invExt)
    (hs : s.objectsAgreeOffReleaseLinks (st.updateSchedContext scId g)) :
    (∀ scId', scId' ≠ scId →
        ((s.updateTcb tid f).getSchedContext? scId').map (·.boundThread)
          = (st.getSchedContext? scId').map (·.boundThread)) ∧
    (((s.updateTcb tid f).getSchedContext? scId).map (·.boundThread)
          = (st.getSchedContext? scId).map (fun sc => (g sc).boundThread)) ∧
    (∀ x, ((s.updateTcb tid f).getTcb? x).map (·.cpuAffinity)
        = (st.getTcb? x).map (·.cpuAffinity)) := by
  have hsSc : ∀ k, (s.getSchedContext? k).map (·.boundThread)
      = ((st.updateSchedContext scId g).getSchedContext? k).map (·.boundThread) :=
    fun k => hs.getSchedContext?_map (·.boundThread) (fun _ => rfl) k
  have hsTcb : ∀ x, s.getTcb? x = (st.updateSchedContext scId g).getTcb? x := hs.getTcb?
  refine ⟨?_, ?_, ?_⟩
  · intro scId' hne
    rw [SystemState.updateTcb_getSchedContext? s tid f hsInv, hsSc,
      SystemState.updateSchedContext_getSchedContext?_ne st scId g hInv scId'
        (fun hEq => hne (SeLe4n.SchedContextId.toObjId_injective _ _ hEq).symm)]
  · rw [SystemState.updateTcb_getSchedContext? s tid f hsInv, hsSc,
      SystemState.updateSchedContext_getSchedContext?_self st scId g hInv]
    cases st.getSchedContext? scId <;> rfl
  · intro x
    by_cases hEq : tid.toObjId = x.toObjId
    · obtain rfl := SeLe4n.ThreadId.toObjId_injective _ _ hEq
      rw [SystemState.updateTcb_getTcb?_self s tid f hsInv, hsTcb,
        SystemState.updateSchedContext_getTcb? st scId g hInv tid]
      cases st.getTcb? tid with
      | none => rfl
      | some t => simp only [Option.map_some, hf]
    · rw [SystemState.updateTcb_getTcb?_ne s tid f hsInv x hEq, hsTcb,
        SystemState.updateSchedContext_getTcb? st scId g hInv x]

/-- The affinity argument of the in-place unbind, over the shape rather than the
arm: the entry class whose obligation the unbind changes is its own
SchedContext's, and post-state that SchedContext is bound to no thread (`hg`),
so those entries' obligations are vacuous wherever they survive; every other
entry keeps its SchedContext's bound thread and every thread its home core, and
its membership descends through the purge, which only ever removes (`hSub`).
Which queue the purge edits is therefore not read here at all — it is what
orphan-freedom (`replenishQueueEntriesBound_smp`) reads — and that is
`schedContextUnbind_preserves_replenishQueueAffinityConsistent_smp`'s own
argument (`SchedContext/BindingAffinity.lean`), restated for this shape. -/
private theorem unbind_shape_preserves_replenishQueueAffinityConsistent_smp
    (st s : SystemState) (scId : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) (hg : ∀ sc, (g sc).boundThread = none)
    (tid : SeLe4n.ThreadId) (f : TCB → TCB) (hf : ∀ t, (f t).cpuAffinity = t.cpuAffinity)
    (hInv : st.objects.invExt) (hsInv : s.objects.invExt)
    (hSub : ∀ c e, e ∈ ((s.updateTcb tid f).scheduler.replenishQueueOnCore c).entries →
      e ∈ (st.scheduler.replenishQueueOnCore c).entries)
    (hs : s.objectsAgreeOffReleaseLinks (st.updateSchedContext scId g))
    (hCons : replenishQueueAffinityConsistent_smp st) :
    replenishQueueAffinityConsistent_smp (s.updateTcb tid f) := by
  obtain ⟨hOther, hSelf, hTgt⟩ :=
    scUpdate_then_tcbUpdate_read_frame st s scId g tid f hf hInv hsInv hs
  intro c scId₀ t hMem sc₀ hSc₀ tid₀ hTid₀
  have hMemPre := hSub c _ hMem
  rw [determineTargetCore_congr _ _ tid₀ (hTgt tid₀)]
  by_cases hk : scId₀ = scId
  · subst hk
    have e := hSelf
    rw [hSc₀] at e
    cases hPre : st.getSchedContext? scId₀ with
    | none => rw [hPre] at e; cases e
    | some scP =>
      rw [hPre] at e
      simp only [Option.map_some, Option.some.injEq, hg scP] at e
      rw [e] at hTid₀; cases hTid₀
  · have e := hOther scId₀ hk
    rw [hSc₀] at e
    cases hPre : st.getSchedContext? scId₀ with
    | none => rw [hPre] at e; cases e
    | some scP =>
      rw [hPre] at e
      simp only [Option.map_some, Option.some.injEq] at e
      exact hCons c scId₀ t hMemPre scP hPre tid₀ (e ▸ hTid₀)

/-- **`v0.35.164`: the in-place unbind preserves replenish-queue affinity, with
no hypothesis on the purge core** -- see the shape lemma above for why the core
is not read.  The `_replenishQueue_purged` / `_replenishQueue_ne` frames supply
the queue readings and `scUpdate_then_tcbUpdate_read_frame` the object ones. -/
theorem cancelBoundDonationOnCore_preserves_replenishQueueAffinityConsistent_smp
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (h : cancelBoundDonationOnCore st tid tcb = .ok st') :
    replenishQueueAffinityConsistent_smp st' := by
  obtain ⟨scId, hBind⟩ := cancelBoundDonationOnCore_ok_bound st st' tid tcb h
  have hSub : ∀ c e, e ∈ (st'.scheduler.replenishQueueOnCore c).entries →
      e ∈ (st.scheduler.replenishQueueOnCore c).entries := fun c e he =>
    (cancelBoundDonationOnCore_replenishQueue_purged st st' tid tcb scId hBind hInv h c e he).1
  simp only [cancelBoundDonationOnCore, hBind] at h
  injection h with h
  subst h
  -- The key hook writes flags alone: transport the invariant across it.
  refine (replenishQueueAffinityConsistent_smp_congr
    (fun c => markKeyChangeFrom_replenishQueueOnCore _ _ _ c)
    (fun scId₀ => markKeyChangeFrom_getSchedContext? _ _ _ scId₀)
    (fun x => determineTargetCore_congr _ _ x (by rw [markKeyChangeFrom_getTcb?]))).mpr ?_
  simp only [markKeyChangeFrom_replenishQueueOnCore] at hSub
  have hInv1 := SystemState.updateSchedContext_preserves_objects_invExt st scId
    (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) hInv
  exact unbind_shape_preserves_replenishQueueAffinityConsistent_smp st _ scId
    (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })
    (fun _ => rfl) tid (fun tcb' => { tcb' with scBindingScCode := 0, scBindingOwnerCode := 0 })
    (fun _ => rfl) hInv (SchedContextOps.purgeReplenishment_objects_invExt _ _ hInv1) hSub
    (SchedContextOps.purgeReplenishment_agree _ _) hCons

/-- **`v0.35.164`: the donated arm preserves replenish-queue affinity** -- the
return then the migration, which is exactly the pair
`migrateSchedContextReplenishment_to_home_preserves_affinityConsistent_smp` is
stated for: the pop wrote no replenish queue, no *other* SchedContext and no
home core, and its success witnesses that the context was bound to the holder,
so the invariant homed its replenishments on the holder's core -- the
migration's source.  The arm's destination is the recorded owner's post-return
home, which is `replenishHomeOfSchedContext` of the post-return state because
the pop bound the context to that owner
(`returnDonatedSchedContext_post_boundThread`).

`hTcb` is what makes the arm's argument the thread the return re-reads: the
return resolves the binding through `lookupTcb` on its own, and an argument
naming a binding the store does not hold would migrate a context the return
never touched.  Both callers pass the stored record (the suspend's G3 through
its re-lookup, the destroy path through the object it is retyping). -/
theorem cancelDonatedDonationOnCore_preserves_replenishQueueAffinityConsistent_smp
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : lookupTcb st tid = some tcb)
    (hInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st') :
    replenishQueueAffinityConsistent_smp st' := by
  unfold cancelDonatedDonationOnCore at h
  split at h
  · rename_i scId originalOwner hBind
    split at h
    · cases h
    · injection h with h
      subst h
      rename_i st1 hClean
      simp only [cleanupDonatedSchedContext, hTcb, hBind] at hClean
      obtain ⟨newOwner?, _, hRet⟩ := returnDonatedSchedContextResolved_ok_decompose hClean
      obtain ⟨scPre, hScPre, hScPreBound⟩ :=
        returnDonatedSchedContext_ok_implies_sc_bound st st1 tid scId originalOwner newOwner? hRet
      obtain ⟨scPost, hScPost, hScPostBound⟩ :=
        returnDonatedSchedContext_post_boundThread st st1 tid scId originalOwner hInv
          newOwner? hRet
      have hSched : st1.scheduler =
          { st.scheduler with reschedulePending := st1.scheduler.reschedulePending } :=
        returnDonatedSchedContext_scheduler_eq st st1 tid scId originalOwner newOwner? hRet
      rw [← replenishHomeOfSchedContext_eq_of_bound st1 scId (determineTargetCore st tid)
        scPost originalOwner hScPost hScPostBound]
      exact migrateSchedContextReplenishment_to_home_preserves_affinityConsistent_smp st st1
        scId (determineTargetCore st tid) scPre tid
        (fun c => by rw [hSched]; rfl)
        (fun scId₀ hne => returnDonatedSchedContext_getSchedContext?_ne st st1 tid scId scId₀
          originalOwner hne hInv newOwner? hRet)
        (fun x => determineTargetCore_congr st st1 x
          (TCB.map_cpuAffinity_of_placement (returnDonatedSchedContext_getTcb?_placement_eq st st1 tid scId originalOwner hInv
            newOwner? hRet x)))
        hScPre hScPreBound rfl hCons
  · cases h

/-- **`v0.35.164`: the dispatcher preserves replenish-queue affinity on every
arm** -- the identity on `.unbound`, the two theorems above on the rest.  This is
the statement both callers consume: the destroy path
(`lifecyclePreRetypeCleanup`, whose retype of a bound or donated thread used to
falsify the invariant) and the suspend pipeline's G3, which had never had one. -/
theorem cancelDonationArmOnCore_preserves_replenishQueueAffinityConsistent_smp
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : lookupTcb st tid = some tcb)
    (hInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (h : cancelDonationArmOnCore st tid tcb = .ok st') :
    replenishQueueAffinityConsistent_smp st' := by
  unfold cancelDonationArmOnCore at h
  split at h
  · injection h with h; subst h; exact hCons
  · exact cancelBoundDonationOnCore_preserves_replenishQueueAffinityConsistent_smp
      _ _ _ _ hInv hCons h
  · exact cancelDonatedDonationOnCore_preserves_replenishQueueAffinityConsistent_smp
      _ _ _ _ hTcb hInv hCons h

/-- **`v0.35.165`: the binding release leaves the replenish queues where the
bound threads are.**

Unconditional, and the reason is worth stating because it is *not*
`schedContextUnbind`'s argument: the release only ever **removes** replenish
entries, and it frames both readings the invariant makes — its one object write
is a TCB's `schedContextBinding`, which moves no scheduling context's record and
no thread's `cpuAffinity`.  An invariant quantified over the entries that are
*present* therefore descends to a state with fewer of them, whatever the
released context's own record still says.  (The unbind needs more because it
rewrites its context to `boundThread := none`, which is a change the invariant
reads.) -/
theorem releaseSchedContextBinding_preserves_replenishQueueAffinityConsistent_smp
    (st : SystemState) (scId : SeLe4n.SchedContextId) (sc : SeLe4n.Kernel.SchedContext)
    (hInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st) :
    replenishQueueAffinityConsistent_smp (releaseSchedContextBinding st scId sc) := by
  unfold releaseSchedContextBinding
  split
  · exact hCons
  · rename_i tid _
    split
    · -- The bound thread resolves: `scId`'s entry is purged from the queue
      -- holding it, and the bound thread unbound.
      rename_i tcb _
      intro c
      refine replenishQueueAffinityConsistentOnCore_transfer st _ c ?_ ?_ ?_ (hCons c)
      · -- Entries: the purge removes, and never adds (and the reschedule-pending
        -- mark writes no replenish queue).
        intro e hMem
        dsimp only at hMem
        rw [markKeyChangeFor_replenishQueueOnCore] at hMem
        have := SchedContextOps.purgeReplenishment_entries_subset _ scId c e hMem
        rwa [SystemState.updateTcb_scheduler] at this
      · -- `boundThread`: the purge writes release fields alone, the TCB write
        -- no context.
        intro k
        dsimp only
        rw [markKeyChangeFor_getSchedContext?,
          (SchedContextOps.purgeReplenishment_agree _ scId).getSchedContext?_map
            (·.boundThread) (fun _ => rfl),
          SystemState.updateTcb_getSchedContext? st tid _ hInv k]
      · -- Home cores: the TCB write moves no `cpuAffinity`.
        intro x
        refine determineTargetCore_congr _ _ x ?_
        dsimp only
        rw [markKeyChangeFor_getTcb?, SchedContextOps.purgeReplenishment_getTcb?]
        by_cases hx : tid.toObjId = x.toObjId
        · have hEq : tid = x := SeLe4n.ThreadId.toObjId_injective _ _ hx
          subst hEq
          rw [SystemState.updateTcb_getTcb?_self st tid _ hInv]
          cases st.getTcb? tid <;> rfl
        · rw [SystemState.updateTcb_getTcb?_ne st tid _ hInv x hx]
    · -- The bound thread is gone from the store: the purge alone.
      intro c
      refine replenishQueueAffinityConsistentOnCore_transfer st _ c ?_ ?_ ?_ (hCons c)
      · intro e hMem
        exact SchedContextOps.purgeReplenishment_entries_subset st scId c e hMem
      · intro k
        exact (SchedContextOps.purgeReplenishment_agree st scId).getSchedContext?_map
          (·.boundThread) (fun _ => rfl) k
      · intro x
        refine determineTargetCore_congr _ _ x ?_
        dsimp only
        rw [SchedContextOps.purgeReplenishment_getTcb?]

/-- After cleanup, the cleaned thread is not in the run queue (the sweep is the
cleanup's first step, so the agreement is read on its input). -/
theorem cleanupTcbReferences_removes_from_runnable
    (st : SystemState) (tid : SeLe4n.ThreadId) (hR : st.runQueueRefined) :
    ¬(tid ∈ ((cleanupTcbReferences st tid).scheduler.runQueueOnCore bootCoreId)) := by
  unfold cleanupTcbReferences
  rw [removeFromNotificationWaitQueue_scheduler_eq]
  rw [removeFromAllEndpointQueues_scheduler_eq]
  exact removeRunnableFromAllCores_not_mem st tid bootCoreId hR

/-- Cleanup preserves lifecycle metadata. -/
theorem cleanupTcbReferences_lifecycle_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cleanupTcbReferences st tid).lifecycle = st.lifecycle := by
  unfold cleanupTcbReferences
  rw [removeFromNotificationWaitQueue_lifecycle_eq,
    removeFromAllEndpointQueues_lifecycle_eq (removeRunnableFromAllCores st tid) tid]
  exact removeRunnableFromAllCores_lifecycle st tid

/-- WS-H2/A-11: Splice every slot of a CNode being replaced out of the
    derivation tree (`spliceDeletedCdtNode`, the delete's own tree step), so no
    edge outlives the CNode: each slot's children are derived from its parent
    instead. -/
def detachCNodeSlots (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) : SystemState :=
  cn.foldCells st (fun acc slot _cap =>
    spliceDeletedCdtNode acc { cnode := cnodeId, slot := slot })

/-- **`detachCNodeSlots` writes the tree and link words alone**: every other
field is the pre-state's. -/
theorem detachCNodeSlots_shape (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    ∃ cdt, SystemState.linkReach { st with cdt := cdt } (detachCNodeSlots st cnodeId cn) := by
  unfold detachCNodeSlots
  exact SeLe4n.Model.CNode.foldCells_preserves cn st _
    (fun acc => ∃ cdt, SystemState.linkReach { st with cdt := cdt } acc)
    ⟨_, .refl _⟩ (fun acc slot _cap _ ⟨c, hAcc⟩ =>
      ⟨_, (hAcc.with_cdt _).trans (spliceDeletedCdtNode_reach acc _)⟩)

/-- `detachCNodeSlots` keeps every object up to derivation links, and the store
invariant. -/
theorem detachCNodeSlots_agree {st : SystemState} (hInv : st.objects.invExt)
    (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    SystemState.objectsAgreeOffDerivationLinks (detachCNodeSlots st cnodeId cn) st ∧
      (detachCNodeSlots st cnodeId cn).objects.invExt := by
  obtain ⟨_, h⟩ := detachCNodeSlots_shape st cnodeId cn
  exact ⟨h.agree hInv, h.invExt hInv⟩

/-- `detachCNodeSlots` preserves lifecycle metadata (CDT-only operation). -/
theorem detachCNodeSlots_lifecycle_eq
    (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    (detachCNodeSlots st cnodeId cn).lifecycle = st.lifecycle := by
  obtain ⟨_, h⟩ := detachCNodeSlots_shape st cnodeId cn; rw [h.fields]

/-- **Splice a slot out of the derivation tree if it holds a capability**
(`spliceDeletedCdtNode`).  An empty slot is outside the tree whenever the tree's
slots hold capabilities (`cdtCompleteness.not_mentions_of_empty`), as seL4's
empty CTE carries no mapping-database node, so it is left alone: the check is
on the slot itself, which the kernel holds, where the tree is ghost state. -/
@[inline] def spliceOccupiedSlot (st : SystemState) (ref : SlotRef) : SystemState :=
  if (st.slotCapAt ref).isSome then spliceDeletedCdtNode st ref else st

/-- `spliceOccupiedSlot` writes the tree and link words alone. -/
theorem spliceOccupiedSlot_shape (st : SystemState) (ref : SlotRef) :
    ∃ cdt, SystemState.linkReach { st with cdt := cdt } (spliceOccupiedSlot st ref) := by
  unfold spliceOccupiedSlot
  split
  · exact ⟨_, spliceDeletedCdtNode_reach st ref⟩
  · exact ⟨st.cdt, .refl _⟩

/-- **Splice both of a thread's space slots out of the derivation tree**
(`spliceOccupiedSlot`, the delete's own tree step on a slot that holds a
capability), as `detachCNodeSlots` does a CNode's: run on a thread being
destroyed, so no edge outlives its CSpace and VSpace root slots (seL4's
`tcbCTable` and `tcbVTable`) and each slot's children are derived from its
parent instead. -/
def detachTcbSlots (st : SystemState) (tcbId : SeLe4n.ObjId) : SystemState :=
  spliceOccupiedSlot
    (spliceOccupiedSlot st { cnode := tcbId, slot := TCB.cspaceRootSlot })
    { cnode := tcbId, slot := TCB.vspaceRootSlot }

/-- **`detachTcbSlots` writes the tree and link words alone**: every other
field is the pre-state's. -/
theorem detachTcbSlots_shape (st : SystemState) (tcbId : SeLe4n.ObjId) :
    ∃ cdt, SystemState.linkReach { st with cdt := cdt } (detachTcbSlots st tcbId) := by
  unfold detachTcbSlots
  obtain ⟨c₁, h₁⟩ := spliceOccupiedSlot_shape st { cnode := tcbId, slot := TCB.cspaceRootSlot }
  obtain ⟨c₂, h₂⟩ := spliceOccupiedSlot_shape
    (spliceOccupiedSlot st { cnode := tcbId, slot := TCB.cspaceRootSlot })
    { cnode := tcbId, slot := TCB.vspaceRootSlot }
  exact ⟨c₂, (h₁.with_cdt c₂).trans h₂⟩

/-- `detachTcbSlots` keeps every object up to derivation links, and the store
invariant. -/
theorem detachTcbSlots_agree {st : SystemState} (hInv : st.objects.invExt)
    (tcbId : SeLe4n.ObjId) :
    SystemState.objectsAgreeOffDerivationLinks (detachTcbSlots st tcbId) st ∧
      (detachTcbSlots st tcbId).objects.invExt := by
  obtain ⟨_, h⟩ := detachTcbSlots_shape st tcbId
  exact ⟨h.agree hInv, h.invExt hInv⟩

/-- `detachTcbSlots` preserves lifecycle metadata. -/
theorem detachTcbSlots_lifecycle_eq (st : SystemState) (tcbId : SeLe4n.ObjId) :
    (detachTcbSlots st tcbId).lifecycle = st.lifecycle := by
  obtain ⟨_, h⟩ := detachTcbSlots_shape st tcbId; rw [h.fields]

/-- `detachTcbSlots` preserves the scheduler. -/
theorem detachTcbSlots_scheduler_eq (st : SystemState) (tcbId : SeLe4n.ObjId) :
    (detachTcbSlots st tcbId).scheduler = st.scheduler := by
  obtain ⟨_, h⟩ := detachTcbSlots_shape st tcbId; rw [h.fields]

/-- `detachTcbSlots` preserves the machine. -/
theorem detachTcbSlots_machine_eq (st : SystemState) (tcbId : SeLe4n.ObjId) :
    (detachTcbSlots st tcbId).machine = st.machine := by
  obtain ⟨_, h⟩ := detachTcbSlots_shape st tcbId; rw [h.fields]

/-- `detachTcbSlots` preserves the TLB-shootdown state. -/
theorem detachTcbSlots_tlbShootdown_eq (st : SystemState) (tcbId : SeLe4n.ObjId) :
    (detachTcbSlots st tcbId).tlbShootdown = st.tlbShootdown := by
  obtain ⟨_, h⟩ := detachTcbSlots_shape st tcbId; rw [h.fields]

-- WS-SM SM6.D (PR #827 review #6): `replyIsStashed` (the server-first stash query —
-- "does any blocked receiver reserve `rid`?") moved down to
-- `SeLe4n.Model.SystemState` (a Model-level object-store fold), so the
-- `endpointReceiveDual` stash guard (`replyStashValid`, below Lifecycle in the
-- import DAG) can reuse it without an IPC→Lifecycle import cycle.  Call it here as
-- `st.replyIsStashed rid` via the `SystemState` namespace.

/-- WS-H2, R4-B.2 (M-13): Pre-retype cleanup combining TCB reference cleanup,
    CDT detach, and service registration cleanup.
    - If the current object is a TCB: refuse a running thread, end its
      reservation the way the suspend's G3 does (`cancelDonationArmOnCore`,
      since `v0.35.164`), then clean up scheduler + IPC references and splice
      its two space slots out of the derivation tree (`detachTcbSlots`).
    - An endpoint is not swept: no registration names one whose back-links
      the retire found clear (`SystemState.tableReferencesRecorded.notTargeted`).
    - If the current object is a CNode: refuse when a slot still records a
      frame mapping or names an installed page table, and otherwise take every
      slot out of the derivation tree as a delete does.  Retype destroys every
      slot the CNode holds, so it owes what `cspaceDeleteSlot` owes for one —
      see the arm for why the detach no longer depends on the replacement's
      shape. -/
def lifecyclePreRetypeCleanup (st : SystemState) (target : SeLe4n.ObjId)
    (currentObj _newObj : KernelObject) : Except KernelError SystemState :=
  -- Z7-P / AJ1-A (M-14): Return donated SchedContext before destroying TCB.
  -- Error propagated — failed cleanup would leave dangling SchedContext refs.
  match (match currentObj with
    | .tcb tcb =>
        -- WS-SM SM8.B (PR #861 review round 39): **refuse to destroy a running
        -- thread.**  The sweep below clears the current slot of whichever core
        -- runs the target — the executing core included, which is where the
        -- caller itself runs — and nothing schedules a successor there.  See
        -- `threadCurrentOnSomeCore`.  `.revocationRequired` is the error this
        -- path already uses for "clear this precondition first" (an in-use
        -- Reply, a TCB still holding a reply link), and reads correctly here as
        -- "suspend or switch away from this thread before destroying it".
        --
        -- Placed inside the arm that already cases on `currentObj`, and reading
        -- the **pre-state** `st`: every later `let` shadows `st` with the swept
        -- state, in which the slot this tests has already been cleared.
        --
        -- **WS-BP BP7.9**: nor a thread whose live FP/SIMD values a core still
        -- holds (`threadHeldOnSomeCore`): that core's release would write them
        -- into whatever TCB the retype creates under this id.
        if threadHeldOnSomeCore st tcb.tid then
          (.error .revocationRequired : Except KernelError SystemState)
        else
          -- **`v0.35.164`: end the reservation the way the suspend's G3 does.**
          -- `cancelDonationArmOnCore` is the suspend pipeline's donation arm,
          -- named: a `.bound` thread's context is unbound with its
          -- replenishment purged from the thread's home core (seL4's
          -- `finaliseCap` → `unbindFromSc`), a `.donated` holder's context is
          -- returned to its owner **and its replenishments migrate** to the
          -- owner's home, an `.unbound` thread is left alone.  Until this
          -- version the arm was the bare `cleanupDonatedSchedContext` — a
          -- return that migrates nothing (register row 57's class, on the
          -- destroy path) — and a `.bound` thread had only its entry in the
          -- (since retired) context-to-threads index removed, leaving the SchedContext bound to a destroyed
          -- thread with its replenishment queued on that thread's home core:
          -- `schedContextBindingConsistent` and
          -- `replenishQueueAffinityConsistent_smp` were both false after a
          -- successful retype, and no theorem claimed either across it.
          cancelDonationArmOnCore st tcb.tid tcb
    | _ => .ok st) with
  | .error e => .error e
  | .ok st =>
  -- **WS-ZA ZA6.6: the yield link, at seL4-MCS's two places.**  The unbind
  -- above is `unbindFromSC`'s `schedContext_unbindTCB`, which then completes
  -- the yield the context records (`completeHeldYield`; the held context's code
  -- is read off the record the caller looked up before any write).  The
  -- reference sweep is the suspend's dequeue and IPC cancel, which `suspend`
  -- ends with the thread's own `schedContext_cancelYieldTo` (`cancelYieldTo`).
  -- A thread's two space slots then leave the derivation tree as a deleted
  -- slot does (`detachTcbSlots`), as a CNode's slots do below.
  let st := match currentObj with
    | .tcb tcb => detachTcbSlots (cancelYieldTo
        (cleanupTcbReferences (completeHeldYield st tcb.scBindingScCode) tcb.tid) tcb.tid) target
    | _ => st
  -- An endpoint needs no registry sweep: the retire admits only an endpoint
  -- recording no registration (`SystemState.tableBackLinksClear`), and on a
  -- state that records its table references no registration then names it
  -- (`SystemState.tableReferencesRecorded.notTargeted`, WS-ZA ZA5.4 part 31).
  match currentObj with
  | .cnode cn =>
    -- **Retype destroys every slot this CNode holds, so it owes what
    -- `cspaceDeleteSlot` owes — for all of them at once.**
    --
    -- Each slot leaves the derivation tree as a deleted one does: its node is
    -- spliced out and its children re-derived from its parent
    -- (`spliceDeletedCdtNode`), so a retype, like a delete, never depends on what
    -- was derived from the slots it destroys.
    --
    -- Both target shapes then detach, which is why this arm no longer reads
    -- `newObj`.  CNode → CNode used to skip the detach on the grounds that no
    -- CDT cleanup was needed; that is wrong, because retype replaces the object
    -- wholesale and the replacement CNode had `slots := UniqueSlotMap.empty`.
    -- No slot survives, so
    -- skipping left every mapping pointing into a CNode that no longer holds
    -- the capability it was minted for: a capability later placed at such a
    -- slot inherits a destroyed one's derivation node, and revoking *that*
    -- node's ancestor takes the unrelated newcomer with it.
    --
    -- **WS-BP BP7.1 (`v0.36.7`): a slot holding a capability that records a
    -- frame mapping cannot be destroyed here** — destroying it owes the
    -- unmapping of what it mapped (seL4's `finaliseCap`), which only the
    -- finalising delete performs (`cspaceDeleteSlotFinalising`); a retype that
    -- dropped it would leave its page mapped with no capability left to name
    -- the mapping.  Refused with the same error: delete those capabilities
    -- first.
    --
    -- WS-BP BP7.1 (`v0.36.12`): nor a capability naming an installed page
    -- table — destroying the last one owes taking the table out of its address
    -- space (`finaliseDestroyedCapabilities`), which only the finalising delete
    -- and revocation perform.
    if cn.holdsFrameMappingRecord || Architecture.cnodeHoldsInstalledPageTableCap st cn then
      .error .revocationRequired
    else
      .ok (detachCNodeSlots st target cn)
  | .reply r =>
    -- WS-SM SM6.D (PR #822 review): reject retyping/deleting a Reply object that
    -- is still in use.  Two in-use forms: (1) a caller is blocked awaiting its
    -- reply (`r.caller.isSome` — caller-first link); (2) a server-first receiver
    -- has stashed this Reply in its `pendingReceiveReply` awaiting its next Call
    -- (`replyIsStashed`, `r.caller` still `none`).  Either way, freeing it strands
    -- the caller / blocks the server (the later `.reply` / the folded server-first
    -- Call link `linkServerStashedReply` fails `.replyCapInvalid`).  Mirrors seL4's
    -- revoke/clear-before-destroy: the
    -- holder must first reply to (or cancel) the outstanding caller, or the server
    -- must re-`Recv`, clearing the link before the object is freed.
    -- PR #822 review: check stashes by the *target* ObjId's canonical ReplyId, not
    -- the reply's internal `r.replyId` field (which can be the `Reply.empty`
    -- sentinel on a freshly retyped object); a server-first receive stashes
    -- `pendingReceiveReply = some (ReplyId.ofNat target)`, so derive the id from
    -- `target` to avoid missing the stash and freeing a still-referenced Reply.
    --
    -- **WS-OD OD5.4 / `v0.35.4`: and a third in-use form — a reply-stack frame.**
    -- A Reply carrying a stack link in either direction (`prev` or `next`) is a
    -- frame of some scheduling context's donation stack, or a frame below a
    -- degenerate (severed) cut still carrying its stale upward link; freeing it
    -- would leave a context's `scReply` or a
    -- neighbour's link naming a slot the retype has replaced.  The one spelling
    -- of "this Reply may be linked or retyped" is `Reply.isFree` — no caller, no
    -- links — shared with `linkReply`, `replyStashValid` and the boot check.
    -- Under `donationChainWellFormed` a linked frame always has a blocked
    -- caller, and a frame whose caller is gone has already left its stack (the
    -- pop, the splice, `Reply.consumed`), so nothing is pinned by this guard
    -- that a cancellation cannot free: the `v0.35.4` finding was exactly a frame
    -- that stayed linked after its caller was consumed.
    if !r.isFree || st.replyStashedAt (SeLe4n.ReplyId.ofNat target.toNat) r then
      .error .revocationRequired
    else .ok st
  | .tcb tcb =>
    -- WS-SM SM6.D (PR #822 review): reject retyping a caller TCB that still holds a
    -- reply link (`replyObject = some rid`, a `blockedOnReply` caller awaiting its
    -- reply).  Freeing the TCB would leave the Reply with `caller = some tid`
    -- pointing at the gone thread, so the later `.reply` resolves a stale caller and
    -- never consumes the Reply.  Mirrors the Reply reject + seL4 revoke-before-
    -- destroy: the outstanding reply must be replied-to / cancelled first.
    --
    -- **WS-ZA ZA4.6: nor a server with callers still waiting on its reply.**
    -- Destroying it left each waiter naming it as its server, and a TCB later
    -- retyped at the same id inherited their priority boost past its own
    -- maximum controlled priority.  A non-empty reply-waiter queue (its head
    -- code is set) refuses the destroy until those callers are answered or
    -- cancelled, as a Reply with a waiting caller is refused above.
    if tcb.replyObject.isSome || tcb.replyWaitersHeadCode != 0 then .error .revocationRequired
    else .ok st
  | .schedContext sc =>
    -- **WS-OD OD5.4: a scheduling context that heads a reply stack cannot be
    -- retyped.**
    --
    -- `donationChainWellFormed.donatedContextResolves` says every Reply naming a
    -- context resolves to a SchedContext object, so freeing one that frames
    -- still name breaks the invariant outright -- and its completeness clause
    -- makes `scReply = none` the exact `O(1)` test for "no frame names it": a
    -- context whose stack is empty holds the whole (empty) chain, so no Reply may
    -- carry its id.  The dual of the `.reply` guard above, and refused for the
    -- same reason: repairing would mean clearing every frame of a stack reachable
    -- only downward.
    -- **`v0.35.165`: and a context that is still BOUND loses its binding.**
    -- The head guard above refuses a context frames still name; it says nothing
    -- about the thread the context is bound to, so a retype used to leave that
    -- thread `.bound scId` (or `.donated scId owner`, the binding a donee holds)
    -- naming an object the slot no longer carries, with `scId`'s replenish entries queued on its home core
    -- under an id the slot's next occupant inherits.  seL4's `finaliseCap` runs
    -- `schedContext_unbindAllTCBs` on a scheduling-context capability;
    -- `releaseSchedContextBinding` is that, per core, composed from
    -- `schedContextUnbind`'s own primitives.
    --
    -- **WS-ZA ZA6.6: and the yield it records is completed**, seL4-MCS's
    -- `finaliseCap` ending `if (sc->scYieldFrom)
    -- schedContext_completeYieldTo(sc->scYieldFrom)`: the yielder is handed
    -- the context's consumed time and both ends of the link are cleared
    -- (`completeYieldFrom`).
    if sc.scReply.isSome then .error .revocationRequired
    else .ok (completeYieldFrom
      (releaseSchedContextBinding st (SeLe4n.SchedContextId.ofObjId target) sc)
      (SeLe4n.SchedContextId.ofObjId target))
  | .frame _ =>
    -- **WS-BP BP7.1: a frame cannot be retyped in place, and that is final.**
    -- A frame *is* a page of physical memory, and a VSpace mapping of it
    -- records that memory's address (`frame.base`), not the object's id.
    -- Replacing the object would leave every such mapping naming memory the
    -- kernel no longer accounts for — a mapping outliving the authority that
    -- created it.  Nor would an unmap here be the right repair: turning a page
    -- of an untyped's memory into a kernel object in place would leave that
    -- memory counted as carved by the untyped's capability and named by nothing.  Memory
    -- goes back where it came from, as in seL4: a frame is destroyed by the
    -- delete of its last capability, which removes the mapping it recorded and
    -- erases the frame, and its pages return to the untyped when the untyped's
    -- capability is reset (`untypedResetFromCap`).  `.revocationRequired` is the
    -- error this path uses for "clear this precondition first" — here, delete
    -- the frame's capabilities and reset the untyped's.
    .error .revocationRequired
  | .pageTable _ =>
    -- **WS-BP BP7.1 (`v0.36.12`): nor can a page table**, for the frame's reason
    -- and one more: a table is a page an address space's slot may name, so
    -- replacing it in place would leave that slot naming a kernel object that is
    -- not a table.  It returns to its untyped through the reset.
    .error .revocationRequired
  | .untyped _ =>
    -- **WS-BP BP7.1 slice 4 (`v0.36.8`): nor can an untyped, for the same
    -- reason one level up.**  An untyped *is* a region of physical memory, and
    -- the objects carved from it — frames, child untypeds and their own carves
    -- — are named by its child list, which the parent's reset refuses while it
    -- is non-empty.  Replacing it in place would orphan every carved object (a
    -- frame whose page no untyped accounts for any more) and, for a child
    -- untyped, leave its parent's child list naming a kernel object no delete
    -- can retire, so one holder of the child's capability could wedge the
    -- parent's reset for good.  seL4 has no in-place retype of an untyped at
    -- all; its memory returns through the untyped it was carved from (its last
    -- capability's delete, then the parent's reset), and a boot untyped is
    -- never destroyed.
    .error .revocationRequired
  | .vspaceRoot _ =>
    -- **`v0.36.35`: nor can a VSpace root — the fourth memory-backed kind, and
    -- the one this match had missed.**  `v0.36.9` refused *creating* a root in
    -- place and nothing refused *destroying*
    -- one: a root fell to the wildcard below, so an in-place retype freed its
    -- ASID and replaced the object while every page table installed under it
    -- kept its page — live leaf descriptors included — and its install record,
    -- which then read as stale (`pageTableInstallLive`).  `pageTableMap`
    -- reinstalls a stale table without zeroing it, so a holder of a `.retype`
    -- right on a root could retype it, let the frames its tables still
    -- translate be reset and recarved to another thread, carve a new root and
    -- reinstall the old table: a hardware walk to that thread's page, writable,
    -- with nothing mapped in the model.  No ASID invalidation was recorded
    -- either, so the freed ASID's stale TLB entries met the next root carved
    -- under it.  The delete of a root's last capability is the path that
    -- retires it — the root leaves the store with its mappings and its ASID is
    -- released behind an acknowledged invalidation round (`retireRecordedObject`)
    -- — so a root goes back where it came from, as every other memory-backed
    -- kind does.
    .error .revocationRequired
  | _ => .ok st

/-- **WS-OD OD5.4 / `v0.35.4`: a Reply that is a reply-stack frame cannot be
retyped.**

The guard, stated: a Reply that is not free — a caller still blocked on it, or a
stack link in either direction — is in use, so destroying it would strand that
caller or leave a stack naming a slot the retype has replaced.
`.revocationRequired` is the error this path already uses for "clear this
precondition first", and it reads correctly here as "let the outstanding call
chain unwind, or cancel it, before freeing the Reply". -/
theorem lifecyclePreRetypeCleanup_reply_refuses_live_stack_frame
    (st : SystemState) (target : SeLe4n.ObjId) (r : Reply) (newObj : KernelObject)
    (hNotFree : r.isFree = false) :
    lifecyclePreRetypeCleanup st target (.reply r) newObj = .error .revocationRequired := by
  unfold lifecyclePreRetypeCleanup
  simp only [hNotFree, Bool.not_false, Bool.true_or, if_true]

/-- The linked forms of the guard: a `prev` link alone, or a `next` link alone,
each refuses the retype. -/
theorem lifecyclePreRetypeCleanup_reply_refuses_prev_link
    (st : SystemState) (target : SeLe4n.ObjId) (r : Reply) (newObj : KernelObject)
    (hPrev : r.prev.isSome = true) :
    lifecyclePreRetypeCleanup st target (.reply r) newObj = .error .revocationRequired :=
  lifecyclePreRetypeCleanup_reply_refuses_live_stack_frame st target r newObj (by
    unfold Reply.isFree
    cases hp : r.prev with
    | none => rw [hp] at hPrev; cases hPrev
    | some _ => simp)

theorem lifecyclePreRetypeCleanup_reply_refuses_next_link
    (st : SystemState) (target : SeLe4n.ObjId) (r : Reply) (newObj : KernelObject)
    (hNext : r.next.isSome = true) :
    lifecyclePreRetypeCleanup st target (.reply r) newObj = .error .revocationRequired :=
  lifecyclePreRetypeCleanup_reply_refuses_live_stack_frame st target r newObj (by
    unfold Reply.isFree
    cases hn : r.next with
    | none => rw [hn] at hNext; cases hNext
    | some _ => simp)

/-- **WS-OD OD5.4: a scheduling context that heads a reply stack cannot be
retyped either.**

The dual of the Reply guard: `donatedContextResolves` requires every Reply naming
a context to resolve, and `headHoldsWholeChain`'s completeness clause makes
`scReply = none` exactly "no Reply names this context".  So `scReply.isSome` is
the `O(1)` test for "frames still point here", and destroying such a context is
refused rather than repaired. -/
theorem lifecyclePreRetypeCleanup_schedContext_refuses_stack_head
    (st : SystemState) (target : SeLe4n.ObjId) (sc : SchedContext) (newObj : KernelObject)
    (hHead : sc.scReply.isSome = true) :
    lifecyclePreRetypeCleanup st target (.schedContext sc) newObj
      = .error .revocationRequired := by
  unfold lifecyclePreRetypeCleanup
  simp only [hHead, if_true]

/-- AN4-G.2 (LIF-M02) — **named `lifecycleCleanupPipeline` wrapper** over
`lifecyclePreRetypeCleanup`. The companion `RetypeTarget` subtype
(AN4-F.4, defined in `Capability/Invariant/Defs.lean`) requires callers
to carry the `cleanupHookDischarged` witness; under WS-RC R4.B that
witness now demands a `ScrubToken` produced by a successful invocation
of this very pipeline (see `ScrubToken.fromCleanup`). External
discharge of the predicate by re-deriving observable post-state facts
alone is structurally impossible. The wrapper composes the three
per-step primitives:

1. `cleanupDonatedSchedContext` (return donated SC before destroying TCB)
2. `cleanupTcbReferences` (scheduler + IPC reference scrub)
3. `detachCNodeSlots` (CDT slot-level detachment)

into a single named entry-point so consumers can reference the pipeline by
name rather than enumerating its steps. The per-step helpers remain public
because proof-chain callers (preservation theorems, cross-subsystem
bridge lemmas) reason about each step individually; the wrapper is a
**pure alias** for documentation consolidation. -/
def lifecycleCleanupPipeline (st : SystemState) (target : SeLe4n.ObjId)
    (currentObj newObj : KernelObject) : Except KernelError SystemState :=
  lifecyclePreRetypeCleanup st target currentObj newObj

/-- AN4-G.2 (LIF-M02): The named wrapper is definitionally equal to
`lifecyclePreRetypeCleanup`. Use when proof contexts destructure the
wrapper by `unfold`. -/
@[simp] theorem lifecycleCleanupPipeline_eq
    (st : SystemState) (target : SeLe4n.ObjId) (currentObj newObj : KernelObject) :
    lifecycleCleanupPipeline st target currentObj newObj
      = lifecyclePreRetypeCleanup st target currentObj newObj := rfl

/-- Pre-retype cleanup only removes elements from the flat list, never adds. -/
theorem cleanupTcbReferences_flat_subset
    (st : SystemState) (tid x : SeLe4n.ThreadId)
    (h : x ∈ ((cleanupTcbReferences st tid).scheduler.runQueueOnCore bootCoreId).toList) :
    x ∈ (st.scheduler.runQueueOnCore bootCoreId).toList := by
  unfold cleanupTcbReferences at h
  rw [removeFromNotificationWaitQueue_scheduler_eq] at h
  rw [removeFromAllEndpointQueues_scheduler_eq] at h
  exact removeRunnableFromAllCores_toList_subset st tid x bootCoreId h

/-- CDT cleanup preserves the scheduler. -/
theorem detachCNodeSlots_scheduler_eq
    (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    (detachCNodeSlots st cnodeId cn).scheduler = st.scheduler := by
  obtain ⟨_, h⟩ := detachCNodeSlots_shape st cnodeId cn; rw [h.fields]

/-- WS-SM SM8.B.2: CDT cleanup writes no register bank. -/
theorem detachCNodeSlots_machine_eq
    (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    (detachCNodeSlots st cnodeId cn).machine = st.machine := by
  obtain ⟨_, h⟩ := detachCNodeSlots_shape st cnodeId cn; rw [h.fields]

/-- WS-SM SM7.B: CDT cleanup is CDT-only — the TLB-shootdown state is
framed. -/
theorem detachCNodeSlots_tlbShootdown_eq
    (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    (detachCNodeSlots st cnodeId cn).tlbShootdown = st.tlbShootdown := by
  obtain ⟨_, h⟩ := detachCNodeSlots_shape st cnodeId cn; rw [h.fields]

/-- Cleanup preserves the scheduler state. -/
theorem cleanupTcbReferences_scheduler_eq_removeRunnableFromAllCores
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cleanupTcbReferences st tid).scheduler
      = (removeRunnableFromAllCores st tid).scheduler := by
  unfold cleanupTcbReferences
  rw [removeFromNotificationWaitQueue_scheduler_eq]
  exact removeFromAllEndpointQueues_scheduler_eq (removeRunnableFromAllCores st tid) tid

/-- **WS-SM SM8.B (PR #861 review round 40): the destroyed-remote-current case
is unreachable.**

A separate finding asked for a `.reschedule` SGI when a retype destroys a TCB
that is current on a **remote** core: the sweep clears that core's slot, the
object then stops being a TCB, and `crossCoreSgiBody` — which opens by matching
the post-state object against a TCB — re-derives nothing, leaving the remote
processor running scrubbed storage.

The round-39 guard closes it by construction rather than by adding a rule: the
cleanup rejects a target current on **any** core, so no retype ever reaches a
state in which a remote core's current slot held the destroyed thread.  Stated
as a theorem because "unreachable" is exactly the kind of claim that rots — if
the guard is ever narrowed to the executing core, this stops compiling. -/
theorem lifecyclePreRetypeCleanup_rejects_current_anywhere
    (st : SystemState) (target : SeLe4n.ObjId) (tcb : TCB) (newObj : KernelObject)
    (c : SeLe4n.Kernel.Concurrency.CoreId)
    (hCur : st.scheduler.currentOnCore c = some tcb.tid) :
    lifecyclePreRetypeCleanup st target (.tcb tcb) newObj = .error .revocationRequired := by
  unfold lifecyclePreRetypeCleanup
  simp only []
  rw [if_pos (by simp [threadHeldOnSomeCore, (threadCurrentOnSomeCore_iff st tcb.tid).mpr ⟨c, hCur⟩])]

/-- WS-SM SM8.B.2: the TCB reference scrub writes no register bank.

The `machine` companion of `cleanupTcbReferences_scheduler_eq_removeRunnableFromAllCores`.
Note the asymmetry, which is the whole point of the pair: the sweep *does* write
scheduler slots (on the cores the thread occupied) and writes `machine` on none,
so the retype's write set is bounded by the former while the latter contributes
nothing. -/
theorem cleanupTcbReferences_machine_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cleanupTcbReferences st tid).machine = st.machine := by
  unfold cleanupTcbReferences
  rw [removeFromNotificationWaitQueue_machine_eq,
      removeFromAllEndpointQueues_machine_eq, removeRunnableFromAllCores_machine]

/-- Pre-retype cleanup flat list subset: any element in the post-cleanup flat
    list was in the pre-cleanup flat list. AJ1-A (M-14): conditional on `.ok`. -/
theorem lifecyclePreRetypeCleanup_flat_subset
    (st stClean : SystemState) (target : SeLe4n.ObjId)
    (currentObj newObj : KernelObject) (x : SeLe4n.ThreadId)
    (hOk : lifecyclePreRetypeCleanup st target currentObj newObj = .ok stClean)
    (h : x ∈ (stClean.scheduler.runQueueOnCore bootCoreId).toList) :
    x ∈ (st.scheduler.runQueueOnCore bootCoreId).toList := by
  cases currentObj with
  | tcb tcb =>
    -- Unfold with known currentObj = .tcb tcb
    simp only [lifecyclePreRetypeCleanup] at hOk
    -- Round 39: the running-target rejection is vacuous on the `.ok` path.
    rw [if_neg (by
      intro hRun
      rw [if_pos hRun] at hOk
      exact absurd hOk (by simp))] at hOk
    -- The inner match is the reservation arm; the outer match dispatches on
    -- its result.
    cases hArm : cancelDonationArmOnCore st tcb.tid tcb with
    | error e => rw [hArm] at hOk; contradiction
    | ok stArm =>
      rw [hArm] at hOk
      -- `v0.35.164`: the arm may purge or migrate a replenish queue, never a run
      -- queue (`cancelDonationArmOnCore_runQueue_current_eq`), which is all the
      -- boot-core flat list below reads.
      have hArmRQ : stArm.scheduler.runQueueOnCore bootCoreId
          = st.scheduler.runQueueOnCore bootCoreId :=
        (cancelDonationArmOnCore_runQueue_current_eq st stArm tcb.tid tcb bootCoreId hArm).1
      -- PR #822 review: with the reservation ended, the final `.tcb` arm rejects a
      -- TCB still holding a reply link (`.error`, vacuous on `.ok`); reduce the
      -- reject-`if` away on the `.ok` path and finish the cleanup-identity proof.
      simp only [] at hOk
      have hRO : (tcb.replyObject.isSome || tcb.replyWaitersHeadCode != 0) = false := by
        cases hr : (tcb.replyObject.isSome || tcb.replyWaitersHeadCode != 0) with
        | false => rfl
        | true => rw [if_pos hr] at hOk; exact absurd hOk (by simp)
      rw [if_neg (by simp only [hRO]; exact Bool.false_ne_true)] at hOk
      injection hOk with hOk; subst hOk
      rw [detachTcbSlots_scheduler_eq, SystemState.cancelYieldTo_scheduler,
        cleanupTcbReferences_scheduler_eq_removeRunnableFromAllCores] at h
      -- Take the sweep off first (it handles its own per-core guard), then
      -- collapse the run-queue-preserving prefix.
      have hSub := removeRunnableFromAllCores_toList_subset _ tcb.tid x bootCoreId h
      rw [SystemState.completeHeldYield_scheduler, hArmRQ] at hSub
      exact hSub
  | cnode cn =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    -- The guard rejects (vacuous on the `.ok` path); past it the state is the
    -- detached one, whose scheduler is framed.
    split at hOk
    · exact absurd hOk (by simp)
    · injection hOk with hOk; subst hOk
      have hSched := detachCNodeSlots_scheduler_eq st target cn
      rw [show ((detachCNodeSlots st target cn).scheduler.runQueueOnCore bootCoreId).toList =
            (st.scheduler.runQueueOnCore bootCoreId).toList from by rw [hSched]] at h
      exact h
  | endpoint _ =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    injection hOk with hOk; subst hOk; exact h
  | notification _ =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    injection hOk with hOk; subst hOk; exact h
  | untyped _ | vspaceRoot _ =>
    -- `v0.36.35`: a VSpace root is refused too (vacuous on `.ok`).
    -- WS-BP BP7.1 slice 4: an untyped target is refused (vacuous on `.ok`).
    simp [lifecyclePreRetypeCleanup] at hOk
  | schedContext _ =>
    -- WS-OD OD5.4: a context that heads a reply stack errors (vacuous on `.ok`).
    -- `v0.35.165`: one that heads none releases the binding it still holds, and
    -- that step writes one TCB, one core's replenish queue and the index — no
    -- run queue on any core (`releaseSchedContextBinding_runQueueOnCore`).
    simp only [lifecyclePreRetypeCleanup] at hOk
    split at hOk
    · cases hOk
    · injection hOk with hOk; subst hOk
      rw [SystemState.completeYieldFrom_scheduler, releaseSchedContextBinding_runQueueOnCore] at h
      exact h
  | reply r =>
    -- WS-SM SM6.D (PR #822 review): an in-use reply errors (vacuous on `.ok`);
    -- a free reply is a scheduler-identity cleanup like the kinds above.
    simp only [lifecyclePreRetypeCleanup] at hOk
    split at hOk
    · cases hOk
    · injection hOk with hOk; subst hOk; exact h
  | frame _ | pageTable _ =>
    -- WS-BP BP7.1: a frame target is refused (vacuous on `.ok`).
    simp [lifecyclePreRetypeCleanup] at hOk

/-- WS-SM SM7.B: the pre-retype cleanup pipeline never touches the
TLB-shootdown state — every step (the reservation arm: an unbind or a
migrating return, since `v0.35.164`; the TCB reference scrub, endpoint
service detachment, CDT slot detachment, reply/TCB in-use rejects) is an
objects/scheduler/CDT/registry-level mutation.  The `pendingBounded` bundle-carriage link for
the SM7.B.11 retype-with-shootdown wrapper; mirrors the case structure
of `lifecyclePreRetypeCleanup_flat_subset`. -/
theorem lifecyclePreRetypeCleanup_tlbShootdown_eq
    (st stClean : SystemState) (target : SeLe4n.ObjId)
    (currentObj newObj : KernelObject)
    (hOk : lifecyclePreRetypeCleanup st target currentObj newObj = .ok stClean) :
    stClean.tlbShootdown = st.tlbShootdown := by
  cases currentObj with
  | tcb tcb =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    -- Round 39: the running-target rejection is vacuous on the `.ok` path.
    rw [if_neg (by
      intro hRun
      rw [if_pos hRun] at hOk
      exact absurd hOk (by simp))] at hOk
    cases hArm : cancelDonationArmOnCore st tcb.tid tcb with
    | error e => rw [hArm] at hOk; contradiction
    | ok stArm =>
      rw [hArm] at hOk
      have hArmShoot : stArm.tlbShootdown = st.tlbShootdown :=
        cancelDonationArmOnCore_tlbShootdown_eq st stArm tcb.tid tcb hArm
      simp only [] at hOk
      have hRO : (tcb.replyObject.isSome || tcb.replyWaitersHeadCode != 0) = false := by
        cases hr : (tcb.replyObject.isSome || tcb.replyWaitersHeadCode != 0) with
        | false => rfl
        | true => rw [if_pos hr] at hOk; exact absurd hOk (by simp)
      rw [if_neg (by simp only [hRO]; exact Bool.false_ne_true)] at hOk
      rw [← Except.ok.inj hOk, detachTcbSlots_tlbShootdown_eq,
        SystemState.cancelYieldTo_tlbShootdown, cleanupTcbReferences_tlbShootdown_eq,
        SystemState.completeHeldYield_tlbShootdown]
      exact hArmShoot
  | cnode cn =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    -- Same shape as the scheduler frame: the guards' reject is vacuous here,
    -- and the detach frames the shootdown state.
    split at hOk
    · exact absurd hOk (by simp)
    · injection hOk with hOk; subst hOk
      exact detachCNodeSlots_tlbShootdown_eq st target cn
  | endpoint _ =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    injection hOk with hOk; subst hOk; rfl
  | notification _ =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    injection hOk with hOk; subst hOk; rfl
  | untyped _ | vspaceRoot _ =>
    -- `v0.36.35`: a VSpace root is refused too (vacuous on `.ok`).
    simp [lifecyclePreRetypeCleanup] at hOk
  | schedContext _ =>
    -- WS-OD OD5.4: the stack-head refusal is vacuous on `.ok`.  `v0.35.165`: the
    -- binding release is shootdown-silent (`releaseSchedContextBinding_tlbShootdown`).
    simp only [lifecyclePreRetypeCleanup] at hOk
    split at hOk
    · cases hOk
    · injection hOk with hOk; subst hOk
      rw [SystemState.completeYieldFrom_tlbShootdown]
      exact releaseSchedContextBinding_tlbShootdown _ _ _
  | reply r =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    split at hOk
    · cases hOk
    · injection hOk with hOk; subst hOk; rfl
  | frame _ | pageTable _ =>
    simp [lifecyclePreRetypeCleanup] at hOk

-- ============================================================================
-- WS-RR RR7.22 (residual)  The endpoint sweep, characterised per key
-- ============================================================================
--
-- `removeFromAllEndpointQueues` is a fold over the *whole* object store, and
-- the fact its consumers need — "afterwards no endpoint still names the swept
-- thread at a queue boundary" — is not a fold invariant: it is false of the
-- accumulator at every key the fold has not reached.  It is a **pointwise**
-- fact, and `RHTable.fold_pointwise` is the lemma that establishes one.
--
-- Naming the fold body is what lets a proof quantify over it.  The equation
-- below is `rfl`, so the copy cannot drift: a change to the operation's body
-- that this one does not mirror fails to elaborate rather than silently
-- leaving the characterisation about a program the kernel no longer runs.

section EndpointSweep

open SeLe4n.Kernel.RobinHood

/-- **WS-RR RR7.22 (residual)**: one neighbour patch of the mid-queue splice,
named — the guarded "rewrite this thread's links if it exists" step that
`spliceOutMidQueueNode` performs twice. -/
def queueNeighbourPatch (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid? : Option SeLe4n.ThreadId) (upd : TCB → TCB) : RHTable SeLe4n.ObjId KernelObject :=
  match nid? with
  | none => objs
  | some nid =>
    match objs[nid.toObjId]? with
    | some (.tcb t) => objs.insert nid.toObjId (.tcb (upd t))
    | _ => objs

/-- **WS-RR RR7.22 (residual)**: the mid-queue splice *is* those two patches.

`rfl`, the same pin `removeFromAllEndpointQueues_eq_fold` is: the decomposition
cannot drift from the operation without failing the build.  Naming the two steps
is what turns a four-deep nested match into two applications of one lemma.

**WS-OD OD3.9**: and the two `upd` functions are now `queueUnlinkPredecessor` /
`queueUnlinkSuccessor` -- the definitions `endpointQueueRemove` uses -- rather
than two lambdas spelled here.  The successor's used to be
`fun n => { n with queuePrev := tcb.queuePrev }`, dropping `queuePPrev`; see
`queueUnlinkSuccessor` for what that cost. -/
theorem spliceOutMidQueueNode_eq_patches (st : SystemState) (tid : SeLe4n.ThreadId) :
    spliceOutMidQueueNode st tid =
      (match lookupTcb st tid with
       | none => st
       | some tcb =>
         { st with objects := (queueNeighbourPatch
             (queueNeighbourPatch st.objects tcb.queuePrev (queueUnlinkPredecessor tcb))
             tcb.queueNext (queueUnlinkSuccessor tcb)) }) := rfl

/-- **WS-OD OD3.5**: a successful `endpointQueueRemove` resolved its endpoint.

The removal's two error arms are the unresolvable object and the wrong-kind
object, and `getEndpoint?` collapses exactly those two; so `.ok` entails the
typed read succeeded, which is what lets `endpointQueueRemove_eq_patches` be
stated on the splicing arm without its callers having to carry the endpoint.

**WS-RR RR8.8 (`v0.35.193`)** relocated it here from
`Lifecycle/Invariant/CancellationReplyShape.lean`, beside the definitions it is
stated over and beside `spliceOutMidQueueNode_eq_patches`, the sibling answer to
the same question.  `InformationFlow/Invariant/Operations.lean` — which owns
`endpointSpliceHigh` and `objects_insert_preserves_projection_high`, and which
states the removal's projection lemma — is incomparable with that module, so one
of the two askers could not reach the pin at all. -/
theorem endpointQueueRemove_ok_getEndpoint?
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hStep : endpointQueueRemove endpointId isReceiveQ tid st = .ok st') :
    ∃ ep, st.getEndpoint? endpointId = some ep := by
  cases hObj : st.objects[endpointId]? with
  | none =>
    simp only [endpointQueueRemove, hObj, SystemState.getObject?] at hStep
    exact absurd hStep (by simp)
  | some obj =>
    cases obj with
    | endpoint ep =>
      exact ⟨ep, (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mpr hObj⟩
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ =>
      simp only [endpointQueueRemove, hObj, SystemState.getObject?] at hStep
      exact absurd hStep (by simp)

/-- **WS-OD OD3.5**: `endpointQueueRemove`'s two link patches **are**
`queueNeighbourPatch`, the same step `spliceOutMidQueueNode` performs twice.

Stated on the arm that splices — the endpoint resolves, the thread resolves —
rather than as a second copy of the whole body: the equation is then about the
program the removal *runs*, its two error arms are `endpointQueueRemove_ok_getEndpoint?`'s
subject rather than this one's, and the store is read through `getEndpoint?`
rather than by re-opening the discriminator the operation has already opened
(AK7 reader hygiene — a `rfl` restatement of a raw match is still a raw match
site as far as every reader, human or scanner, is concerned).

The tree had two inlined copies of this shape and one named abstraction over it;
naming the third is what makes the removal's write set one lemma rather than a
four-deep nested match.  The two `upd` functions are the shared
`queueUnlinkPredecessor` / `queueUnlinkSuccessor` (WS-OD OD3.9) — the definitions
`endpointQueueRemove` itself applies and `spliceOutMidQueueNode_eq_patches` names
— so the two removals' write sets are stated over one spelling rather than over a
lambda each that could drift apart.  The successor's carries `queuePPrev`
(WS-OD OD1.1), which is why the two patches take different updates and not
one.

**WS-RR RR8.8 (`v0.35.193`)**: relocated here (see
`endpointQueueRemove_ok_getEndpoint?` for why), and the *boundary* and the *link
clear* are now spelled through `queueRemoveBoundary` and `tcbWithQueueLinks` —
the two records WS-RR RR8.4 introduced so the three removals write one value
rather than three authors agreeing.  This pin had restated both inline, which is
a live instance of the duplication RR8.4 removed: the equation is still `rfl`,
so a reader who follows it reaches the shared names rather than a second copy of
what they unfold to. -/
theorem endpointQueueRemove_eq_patches (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st : SystemState) (ep : Endpoint) (tcb : TCB)
    (hEp : st.getEndpoint? endpointId = some ep)
    (hTcb : lookupTcb st tid = some tcb) :
    endpointQueueRemove endpointId isReceiveQ tid st =
      (let q := if isReceiveQ then ep.receiveQ else ep.sendQ
       let objs := queueNeighbourPatch
         (queueNeighbourPatch st.objects tcb.queuePrev (queueUnlinkPredecessor tcb))
         tcb.queueNext (queueUnlinkSuccessor tcb)
       let q' : IntrusiveQueue := queueRemoveBoundary q tid tcb
       let ep' := if isReceiveQ then (ep.withReceiveQ q') else (ep.withSendQ q')
       .ok { st with objects :=
         ((objs.insert endpointId (.endpoint ep')).insert tid.toObjId
           (.tcb (tcbWithQueueLinks tcb none none none))) }) := by
  unfold endpointQueueRemove SystemState.getObject?
  rw [(SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hEp, hTcb]
  rfl

theorem queueNeighbourPatch_invExt (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid? : Option SeLe4n.ThreadId) (upd : TCB → TCB) (hInv : objs.invExt) :
    (queueNeighbourPatch objs nid? upd).invExt := by
  unfold queueNeighbourPatch
  split
  · exact hInv
  · split
    · exact RHTable.insert_preserves_invExt _ _ _ hInv
    · exact hInv

/-- WS-ZA ZA5.11: a neighbour patch whose update keeps a thread's taint words
keeps every slot's. -/
theorem queueNeighbourPatch_sameTaintWords (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid? : Option SeLe4n.ThreadId) (upd : TCB → TCB) (hInv : objs.invExt)
    (hU : ∀ t, (upd t).taintWords = t.taintWords := by taint_words_kept) :
    SameTaintWords objs (queueNeighbourPatch objs nid? upd) := by
  unfold queueNeighbourPatch
  split
  · exact .refl _
  · split
    · next t hAt => exact .insert_tcb hInv hAt (hU t)
    · exact .refl _

/-- WS-ZA ZA5.11: the mid-queue splice keeps every slot's taint words. -/
theorem spliceOutMidQueueNode_sameTaintWords (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    SameTaintWords st.objects (spliceOutMidQueueNode st tid).objects := by
  rw [spliceOutMidQueueNode_eq_patches]
  split
  · exact .refl _
  · rename_i tcb _
    exact (queueNeighbourPatch_sameTaintWords _ _ _ hInv).trans
      (queueNeighbourPatch_sameTaintWords _ _ _ (queueNeighbourPatch_invExt _ _ _ hInv))

/-- A neighbour patch installs only TCBs, so a non-TCB reading is the input's,
in both directions. -/
theorem queueNeighbourPatch_nonTcb (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid? : Option SeLe4n.ThreadId) (upd : TCB → TCB)
    (hInv : objs.invExt) (k : SeLe4n.ObjId) (o : KernelObject)
    (hNotTcb : ∀ t, o ≠ .tcb t) :
    ((queueNeighbourPatch objs nid? upd)[k]? = some o) ↔ (objs[k]? = some o) := by
  unfold queueNeighbourPatch
  split
  · exact Iff.rfl
  · rename_i nid
    split
    · rename_i t hRead
      by_cases hK : nid.toObjId = k
      · subst hK
        constructor
        · intro h
          have h' : (objs.insert nid.toObjId (KernelObject.tcb (upd t))).get? nid.toObjId
              = some o := h
          rw [RHTable.getElem?_insert_self objs nid.toObjId (.tcb (upd t)) hInv] at h'
          exact absurd (Option.some.inj h').symm (hNotTcb (upd t))
        · intro h
          rw [hRead] at h
          exact absurd (Option.some.inj h).symm (hNotTcb t)
      · constructor
        · intro h
          have h' : (objs.insert nid.toObjId (KernelObject.tcb (upd t))).get? k = some o := h
          rwa [RHTable.getElem?_insert_ne objs nid.toObjId k (.tcb (upd t))
            (fun hbeq => hK (eq_of_beq hbeq)) hInv] at h'
        · intro h
          show (objs.insert nid.toObjId (KernelObject.tcb (upd t))).get? k = some o
          rw [RHTable.getElem?_insert_ne objs nid.toObjId k (.tcb (upd t))
            (fun hbeq => hK (eq_of_beq hbeq)) hInv]
          exact h
    · exact Iff.rfl

/-- A neighbour patch read backwards: every TCB it leaves is a queue-link
rewrite of one the input held at the same key. -/
theorem queueNeighbourPatch_backward (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid? : Option SeLe4n.ThreadId) (upd : TCB → TCB)
    (hUpd : ∀ t, tcbQueueLinkRewrite (upd t) t)
    (hInv : objs.invExt) (k : SeLe4n.ObjId) (t' : TCB)
    (hPost : (queueNeighbourPatch objs nid? upd)[k]? = some (.tcb t')) :
    ∃ t0, objs[k]? = some (.tcb t0) ∧ tcbQueueLinkRewrite t' t0 := by
  unfold queueNeighbourPatch at hPost
  split at hPost
  · exact ⟨t', hPost, tcbQueueLinkRewrite.refl t'⟩
  · rename_i nid
    split at hPost
    · rename_i t hRead
      by_cases hK : nid.toObjId = k
      · subst hK
        have hPost' : (objs.insert nid.toObjId (KernelObject.tcb (upd t))).get? nid.toObjId
            = some (KernelObject.tcb t') := hPost
        rw [RHTable.getElem?_insert_self objs nid.toObjId (.tcb (upd t)) hInv] at hPost'
        obtain rfl : upd t = t' := KernelObject.tcb.inj (Option.some.inj hPost')
        exact ⟨t, hRead, hUpd t⟩
      · have hPost' : (objs.insert nid.toObjId (KernelObject.tcb (upd t))).get? k
            = some (KernelObject.tcb t') := hPost
        rw [RHTable.getElem?_insert_ne objs nid.toObjId k (.tcb (upd t))
          (fun hbeq => hK (eq_of_beq hbeq)) hInv] at hPost'
        exact ⟨t', hPost', tcbQueueLinkRewrite.refl t'⟩
    · exact ⟨t', hPost, tcbQueueLinkRewrite.refl t'⟩

/-- **WS-RR RR8.3**: a neighbour patch preserves the `queuePPrev`/`queuePrev`
pairing whenever its update does.

Stated over the update rather than over the operation, because that is where the
obligation lives: `queueUnlinkPredecessor` writes only `queueNext` and
`queueUnlinkSuccessor` writes the removed thread's *own* pair, so both keep the
two fields together — which is the whole of WS-OD OD1.1 and OD3.9, each of which
found a removal writing `queuePrev` alone. -/
theorem queueNeighbourPatch_preserves_queuePPrevAgreesWithPrev
    (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid? : Option SeLe4n.ThreadId) (upd : TCB → TCB)
    (hUpd : ∀ t, t.queuePPrevAgreesWithPrev → (upd t).queuePPrevAgreesWithPrev)
    (hInv : objs.invExt)
    (hPre : ∀ (k : SeLe4n.ObjId) (t : TCB), objs[k]? = some (.tcb t) →
      t.queuePPrevAgreesWithPrev)
    (k : SeLe4n.ObjId) (t' : TCB)
    (hPost : (queueNeighbourPatch objs nid? upd)[k]? = some (.tcb t')) :
    t'.queuePPrevAgreesWithPrev := by
  unfold queueNeighbourPatch at hPost
  split at hPost
  · exact hPre k t' hPost
  · rename_i nid
    split at hPost
    · rename_i t hRead
      by_cases hK : nid.toObjId = k
      · subst hK
        have hPost' : (objs.insert nid.toObjId (KernelObject.tcb (upd t))).get? nid.toObjId
            = some (KernelObject.tcb t') := hPost
        rw [RHTable.getElem?_insert_self objs nid.toObjId (.tcb (upd t)) hInv] at hPost'
        obtain rfl : upd t = t' := KernelObject.tcb.inj (Option.some.inj hPost')
        exact hUpd t (hPre _ t hRead)
      · have hPost' : (objs.insert nid.toObjId (KernelObject.tcb (upd t))).get? k
            = some (KernelObject.tcb t') := hPost
        rw [RHTable.getElem?_insert_ne objs nid.toObjId k (.tcb (upd t))
          (fun hbeq => hK (eq_of_beq hbeq)) hInv] at hPost'
        exact hPre k t' hPost'
    · exact hPre k t' hPost

/-- **WS-RR RR8.3**: the mid-queue splice preserves the pairing — the third
endpoint-queue removal's own statement, composed from the two patches.

`spliceOutMidQueueNode` is run by `.tcbSuspend` and by thread destruction, so it
needs this on its own and not only through the cancellation composite that wraps
it.  The successor patch's obligation is the *removed* thread's pairing, which the
pre-state supplies; the predecessor's is the predecessor's own. -/
theorem spliceOutMidQueueNode_preserves_queuePPrevAgreesWithPrev
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt)
    (hPre : queuePPrevAgreesWithPrev st) :
    queuePPrevAgreesWithPrev (spliceOutMidQueueNode st tid) := by
  have hPreAt : ∀ (a : SeLe4n.ObjId) (t : TCB), st.objects[a]? = some (.tcb t) →
      t.queuePPrevAgreesWithPrev := fun a t hA => hPre ⟨a.toNat⟩ t (by simpa using hA)
  intro k t' hPost
  rw [spliceOutMidQueueNode_eq_patches] at hPost
  revert hPost
  split
  · intro hPost; exact hPre k t' hPost
  · rename_i tcb hLk
    intro hPost
    have hRemoved : tcb.queuePPrevAgreesWithPrev :=
      hPre tid tcb (lookupTcb_some_objects st tid tcb hLk)
    -- The predecessor patch first: it writes only `queueNext`, so the
    -- predecessor keeps its own pair.
    have hMid : ∀ (a : SeLe4n.ObjId) (t : TCB),
        (queueNeighbourPatch st.objects tcb.queuePrev (queueUnlinkPredecessor tcb))[a]?
          = some (.tcb t) → t.queuePPrevAgreesWithPrev :=
      queueNeighbourPatch_preserves_queuePPrevAgreesWithPrev st.objects
        tcb.queuePrev (queueUnlinkPredecessor tcb)
        (fun _ h => TCB.queuePPrevAgreesWithPrev_queueUnlinkPredecessor h) hInv hPreAt
    -- ...then the successor patch, whose obligation is the *removed* thread's pair.
    exact queueNeighbourPatch_preserves_queuePPrevAgreesWithPrev _ tcb.queueNext
      (queueUnlinkSuccessor tcb)
      (fun _ _ => TCB.queuePPrevAgreesWithPrev_queueUnlinkSuccessor hRemoved)
      (queueNeighbourPatch_invExt _ _ _ hInv) hMid k.toObjId t' hPost

/-- **WS-RR RR7.22 (residual)**: the mid-queue splice rewrites **only** intrusive
queue links — every TCB it leaves is a link rewrite of the one it found, and
every non-TCB object is untouched.

This is the whole of what the splice does to the object store, and it is what
lets the conjuncts that read `ipcState`, `schedContextBinding`, `replyObject`,
`pendingMessage`, `timeoutBudget` or `pendingReceiveReply` cross it for free. -/
theorem spliceOutMidQueueNode_tcb_backward
    (st : SystemState) (tid : SeLe4n.ThreadId) (k : SeLe4n.ObjId) (t' : TCB)
    (hInv : st.objects.invExt)
    (hPost : (spliceOutMidQueueNode st tid).objects[k]? = some (.tcb t')) :
    ∃ t0, st.objects[k]? = some (.tcb t0) ∧ tcbQueueLinkRewrite t' t0 := by
  rw [spliceOutMidQueueNode_eq_patches] at hPost
  split at hPost
  · exact ⟨t', hPost, tcbQueueLinkRewrite.refl t'⟩
  · rename_i tcb hT
    obtain ⟨t1, h1, r1⟩ := queueNeighbourPatch_backward _ tcb.queueNext _
      (fun n => ⟨tcb.queuePrevCode, tcb.queuePPrevCode, n.queueNextCode, n.ntfnPrevCode,
        n.ntfnNextCode, rfl⟩)
      (queueNeighbourPatch_invExt _ _ _ hInv) k t' hPost
    obtain ⟨t0, h0, r0⟩ := queueNeighbourPatch_backward st.objects tcb.queuePrev _
      (fun p => ⟨p.queuePrevCode, p.queuePPrevCode, tcb.queueNextCode, p.ntfnPrevCode,
        p.ntfnNextCode, rfl⟩) hInv k t1 h1
    exact ⟨t0, h0, r1.trans r0⟩

/-- **WS-RR RR7.22 (residual)**: the mid-queue splice leaves every non-TCB object
exactly as it found it. -/
theorem spliceOutMidQueueNode_nonTcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (o : KernelObject)
    (hNotTcb : ∀ t, o ≠ .tcb t) :
    ((spliceOutMidQueueNode st tid).objects[k]? = some o) ↔ (st.objects[k]? = some o) := by
  rw [spliceOutMidQueueNode_eq_patches]
  split
  · exact Iff.rfl
  · rename_i tcb hT
    exact (queueNeighbourPatch_nonTcb _ tcb.queueNext _
        (queueNeighbourPatch_invExt _ _ _ hInv) k o hNotTcb).trans
      (queueNeighbourPatch_nonTcb st.objects tcb.queuePrev _ hInv k o hNotTcb)

/-- **`v0.35.166`: the mid-queue splice frames every thread's home core.**

`determineTargetCore` reads one field — `cpuAffinity` — through `getTcb?`, and the
splice patches intrusive queue links only, so it moves no thread.  Stated in the
`Option.map` form `determineTargetCore_congr` consumes, which is what makes the
`none` case load-bearing: the splice materialises no thread where none was, which
`spliceOutMidQueueNode_tcb_backward` is exactly the statement of.

It lives here, beside the two readings its proof composes, rather than in the
cancellation bundle that first needed it (WS-RR RR8.11 wrote it `private` there,
downstream of both the destroy path and the retype wrapper — so the retype's own
reservation theorems could not be stated at all until `v0.35.166` moved it). -/
theorem spliceOutMidQueueNode_tcbField_frame {α : Type} (f : TCB → α)
    (hf : ∀ (t : TCB) qp qpp qn np nn,
      f { t with
        queuePrevCode := qp, queuePPrevCode := qpp, queueNextCode := qn,
        ntfnPrevCode := np, ntfnNextCode := nn } = f t)
    (st : SystemState) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (x : SeLe4n.ThreadId) :
    ((spliceOutMidQueueNode st tid).getTcb? x).map f = (st.getTcb? x).map f := by
  refine SystemState.map_tcbField_eq_of_refines f (fun t0 hT0 => ?_) (fun t' hT' => ?_)
  · obtain ⟨t', hL', hRw'⟩ := spliceOutMidQueueNode_tcb_lookup st tid x.toObjId t0 hInv
      ((SystemState.getTcb?_eq_some_iff st x t0).mp hT0)
    exact ⟨t', (SystemState.getTcb?_eq_some_iff _ x t').mpr hL', hRw'.field f hf⟩
  · obtain ⟨t0, hL0, _⟩ := spliceOutMidQueueNode_tcb_backward st tid x.toObjId t' hInv
      ((SystemState.getTcb?_eq_some_iff _ x t').mp hT')
    exact ⟨t0, (SystemState.getTcb?_eq_some_iff st x t0).mpr hL0⟩

/-- The `TCB.placement` instance: the home core `determineTargetCore_congr`
consumes and the run-queue links the link agreement reads. -/
theorem spliceOutMidQueueNode_placement_frame (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((spliceOutMidQueueNode st tid).getTcb? x).map TCB.placement
      = (st.getTcb? x).map TCB.placement :=
  spliceOutMidQueueNode_tcbField_frame TCB.placement (fun _ _ _ _ _ _ => rfl) st tid hInv x

/-- **`v0.35.183` (register row 63)**: the `schedContextBinding` instance, which
`schedContextBindingConsistent_transfer` consumes.

The splice writes link fields, so a thread's binding crosses it untouched — and
that is the *whole* of what the destroy path's reference sweep needs from this
step, since the sweep's other three phases write endpoints, notifications and
`SchedContext.donationOrigin`. -/
theorem spliceOutMidQueueNode_binding_frame (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((spliceOutMidQueueNode st tid).getTcb? x).map (·.schedContextBinding)
      = (st.getTcb? x).map (·.schedContextBinding) :=
  spliceOutMidQueueNode_tcbField_frame (·.schedContextBinding) (fun _ _ _ _ _ _ => rfl)
    st tid hInv x

-- The precise per-key readings of the two neighbour patches: what the splice
-- installs at each key it touches, and what it leaves at every key it does not.
-- These are what the queue-shape conjuncts read; the `tcbQueueLinkRewrite`
-- backward frame above is what every *other* conjunct reads.

theorem queueNeighbourPatch_at_self (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid : SeLe4n.ThreadId) (upd : TCB → TCB) (hInv : objs.invExt) (t0 : TCB)
    (hk : objs[nid.toObjId]? = some (.tcb t0)) :
    (queueNeighbourPatch objs (some nid) upd)[nid.toObjId]? = some (.tcb (upd t0)) := by
  unfold queueNeighbourPatch
  simp only
  rw [hk]
  exact RHTable.getElem?_insert_self objs nid.toObjId (.tcb (upd t0)) hInv

theorem queueNeighbourPatch_at_other (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid? : Option SeLe4n.ThreadId) (upd : TCB → TCB) (hInv : objs.invExt)
    (k : SeLe4n.ObjId) (hNe : ∀ nid, nid? = some nid → nid.toObjId ≠ k) :
    (queueNeighbourPatch objs nid? upd)[k]? = objs[k]? := by
  unfold queueNeighbourPatch
  split
  · rfl
  · rename_i nid
    have hn : nid.toObjId ≠ k := hNe nid rfl
    split
    · rename_i t hRead
      show (objs.insert nid.toObjId (KernelObject.tcb (upd t))).get? k = objs[k]?
      exact RHTable.getElem?_insert_ne objs nid.toObjId k _ (by simpa using hn) hInv
    · rfl

/-- **WS-RR RR7.22 (residual)**: the splice does not touch the swept thread's own
TCB.  It patches only that thread's two neighbours, and a thread that is its own
neighbour would close a one-step `queueNext` cycle. -/
theorem spliceOutMidQueueNode_victim_tcb (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt)
    (hLink : tcbQueueLinkIntegrity st) (hAcyc : tcbQueueChainAcyclic st)
    (hLookup : lookupTcb st tid = some tcb) :
    (spliceOutMidQueueNode st tid).objects[tid.toObjId]? = some (.tcb tcb) := by
  have hTcb : st.objects[tid.toObjId]? = some (.tcb tcb) :=
    lookupTcb_some_objects st tid tcb hLookup
  have hPrevNe : ∀ p, tcb.queuePrev = some p → p.toObjId ≠ tid.toObjId := by
    intro p hp hEq
    obtain ⟨tA, hA, hAN⟩ := hLink.2 tid tcb hTcb p hp
    rw [hEq, hTcb] at hA
    have hEqT : tA = tcb := (KernelObject.tcb.inj (Option.some.inj hA)).symm
    rw [hEqT] at hAN
    exact hAcyc tid (.single tid tid tcb hTcb hAN)
  have hNextNe : ∀ n, tcb.queueNext = some n → n.toObjId ≠ tid.toObjId := by
    intro n hn hEq
    have hn' : tcb.queueNext = some tid := by
      rw [hn]; exact congrArg some (SeLe4n.ThreadId.toObjId_injective _ _ hEq)
    exact hAcyc tid (.single tid tid tcb hTcb hn')
  rw [spliceOutMidQueueNode_eq_patches, hLookup]
  simp only
  rw [queueNeighbourPatch_at_other _ tcb.queueNext _
    (queueNeighbourPatch_invExt _ _ _ hInv) tid.toObjId hNextNe]
  rw [queueNeighbourPatch_at_other st.objects tcb.queuePrev _ hInv tid.toObjId hPrevNe]
  exact hTcb


theorem queueNeighbourPatch_at_self' (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid? : Option SeLe4n.ThreadId) (nid : SeLe4n.ThreadId) (upd : TCB → TCB)
    (hInv : objs.invExt) (t0 : TCB) (hn : nid? = some nid)
    (hk : objs[nid.toObjId]? = some (.tcb t0)) :
    (queueNeighbourPatch objs nid? upd)[nid.toObjId]? = some (.tcb (upd t0)) := by
  subst hn; exact queueNeighbourPatch_at_self objs nid upd hInv t0 hk

theorem queueNeighbourPatch_tcb_forward (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid? : Option SeLe4n.ThreadId) (upd : TCB → TCB) (hInv : objs.invExt)
    (k : SeLe4n.ObjId) (t0 : TCB) (hk : objs[k]? = some (.tcb t0)) :
    ∃ t', (queueNeighbourPatch objs nid? upd)[k]? = some (.tcb t') ∧
      (t' = t0 ∨ t' = upd t0) := by
  cases hn : nid? with
  | none =>
    exact ⟨t0, by
      rw [queueNeighbourPatch_at_other objs none upd hInv k (by intro n h; cases h)]
      exact hk, Or.inl rfl⟩
  | some nid =>
    by_cases hK : nid.toObjId = k
    · subst hK
      exact ⟨upd t0, queueNeighbourPatch_at_self objs nid upd hInv t0 hk, Or.inr rfl⟩
    · exact ⟨t0, by
        rw [queueNeighbourPatch_at_other objs (some nid) upd hInv k
          (by intro n h; cases h; exact hK)]
        exact hk, Or.inl rfl⟩

/-- **WS-RR RR7.22 (residual)**: after the splice the swept thread's successor
points back **past** it — the skip the splice installs. -/
theorem spliceOutMidQueueNode_next_queuePrev (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (nextTid : SeLe4n.ThreadId) (nextTcb : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st tid = some tcb)
    (hN : tcb.queueNext = some nextTid)
    (hNext : st.objects[nextTid.toObjId]? = some (.tcb nextTcb)) :
    ∃ t', (spliceOutMidQueueNode st tid).objects[nextTid.toObjId]? = some (.tcb t') ∧
      t'.queuePrev = tcb.queuePrev := by
  obtain ⟨t1, h1, _⟩ := queueNeighbourPatch_tcb_forward st.objects tcb.queuePrev
    (queueUnlinkPredecessor tcb) hInv nextTid.toObjId nextTcb hNext
  refine ⟨(queueUnlinkSuccessor tcb t1), ?_, rfl⟩
  rw [spliceOutMidQueueNode_eq_patches, hLookup]
  simp only
  exact queueNeighbourPatch_at_self' _ tcb.queueNext nextTid _
    (queueNeighbourPatch_invExt _ _ _ hInv) t1 hN h1

/-- **WS-OD OD3.9**: after the splice the swept thread's successor carries the
swept thread's own `queuePPrev` -- the back-pointer half of the skip.

The `queuePrev` half above was stated from the day the splice existed; this half
was not, because the splice did not write it.  A successor left naming the swept
thread fails `endpointQueueRemoveDual`'s `pprevConsistent` check in every case it
has a successor at all, so it could never leave the endpoint queue again -- the
defect WS-OD OD1.1 closed in `endpointQueueRemove` and this cut closed here. -/
theorem spliceOutMidQueueNode_next_queuePPrev (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (nextTid : SeLe4n.ThreadId) (nextTcb : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st tid = some tcb)
    (hN : tcb.queueNext = some nextTid)
    (hNext : st.getTcb? nextTid = some nextTcb) :
    ∃ t', (spliceOutMidQueueNode st tid).getTcb? nextTid = some t' ∧
      t'.queuePPrev = tcb.queuePPrev := by
  obtain ⟨t1, h1, _⟩ := queueNeighbourPatch_tcb_forward st.objects tcb.queuePrev
    (queueUnlinkPredecessor tcb) hInv nextTid.toObjId nextTcb
    ((SystemState.getTcb?_eq_some_iff st nextTid nextTcb).mp hNext)
  refine ⟨queueUnlinkSuccessor tcb t1,
    (SystemState.getTcb?_eq_some_iff _ nextTid _).mpr ?_, rfl⟩
  rw [spliceOutMidQueueNode_eq_patches, hLookup]
  simp only
  exact queueNeighbourPatch_at_self' _ tcb.queueNext nextTid _
    (queueNeighbourPatch_invExt _ _ _ hInv) t1 hN h1

/-- **WS-RR RR7.22 (residual)**: after the splice the swept thread's predecessor
points **past** it. -/
theorem spliceOutMidQueueNode_prev_queueNext (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (prevTid : SeLe4n.ThreadId) (prevTcb : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st tid = some tcb)
    (hP : tcb.queuePrev = some prevTid)
    (hPrev : st.objects[prevTid.toObjId]? = some (.tcb prevTcb)) :
    ∃ t', (spliceOutMidQueueNode st tid).objects[prevTid.toObjId]? = some (.tcb t') ∧
      t'.queueNext = tcb.queueNext := by
  have hInner : (queueNeighbourPatch st.objects tcb.queuePrev
      (queueUnlinkPredecessor tcb))[prevTid.toObjId]?
      = some (.tcb (queueUnlinkPredecessor tcb prevTcb)) :=
    queueNeighbourPatch_at_self' st.objects tcb.queuePrev prevTid _ hInv prevTcb hP hPrev
  obtain ⟨t1, h1, hcase⟩ := queueNeighbourPatch_tcb_forward _ tcb.queueNext
    (queueUnlinkSuccessor tcb)
    (queueNeighbourPatch_invExt _ _ _ hInv) prevTid.toObjId
    (queueUnlinkPredecessor tcb prevTcb) hInner
  refine ⟨t1, ?_, ?_⟩
  · rw [spliceOutMidQueueNode_eq_patches, hLookup]
    simp only
    exact h1
  · rcases hcase with rfl | rfl <;> rfl

/-- Every thread that is not the swept thread's successor keeps its `queuePrev`. -/
theorem spliceOutMidQueueNode_queuePrev_frame (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (k : SeLe4n.ObjId) (t0 : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st tid = some tcb)
    (hk : st.objects[k]? = some (.tcb t0))
    (hNe : ∀ n, tcb.queueNext = some n → n.toObjId ≠ k) :
    ∃ t', (spliceOutMidQueueNode st tid).objects[k]? = some (.tcb t') ∧
      t'.queuePrev = t0.queuePrev := by
  obtain ⟨t1, h1, hcase⟩ := queueNeighbourPatch_tcb_forward st.objects tcb.queuePrev
    (queueUnlinkPredecessor tcb) hInv k t0 hk
  refine ⟨t1, ?_, ?_⟩
  · rw [spliceOutMidQueueNode_eq_patches, hLookup]
    simp only
    rw [queueNeighbourPatch_at_other _ tcb.queueNext _
      (queueNeighbourPatch_invExt _ _ _ hInv) k hNe]
    exact h1
  · rcases hcase with rfl | rfl <;> rfl

/-- **PR #897 review (`v0.35.106`)**: ...and its `queuePPrev`, for the same reason
— `queueUnlinkPredecessor` writes `queueNext` alone.  The head boundary carries the
pair now, so a consumer that framed only `queuePrev` framed half a back-pointer. -/
theorem spliceOutMidQueueNode_queuePPrev_frame (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (k : SeLe4n.ObjId) (t0 : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st tid = some tcb)
    (hk : st.objects[k]? = some (.tcb t0))
    (hNe : ∀ n, tcb.queueNext = some n → n.toObjId ≠ k) :
    ∃ t', (spliceOutMidQueueNode st tid).objects[k]? = some (.tcb t') ∧
      t'.queuePPrev = t0.queuePPrev := by
  obtain ⟨t1, h1, hcase⟩ := queueNeighbourPatch_tcb_forward st.objects tcb.queuePrev
    (queueUnlinkPredecessor tcb) hInv k t0 hk
  refine ⟨t1, ?_, ?_⟩
  · rw [spliceOutMidQueueNode_eq_patches, hLookup]
    simp only
    rw [queueNeighbourPatch_at_other _ tcb.queueNext _
      (queueNeighbourPatch_invExt _ _ _ hInv) k hNe]
    exact h1
  · rcases hcase with rfl | rfl <;> rfl

/-- Every thread that is not the swept thread's predecessor keeps its `queueNext`. -/
theorem spliceOutMidQueueNode_queueNext_frame (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (k : SeLe4n.ObjId) (t0 : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st tid = some tcb)
    (hk : st.objects[k]? = some (.tcb t0))
    (hNe : ∀ p, tcb.queuePrev = some p → p.toObjId ≠ k) :
    ∃ t', (spliceOutMidQueueNode st tid).objects[k]? = some (.tcb t') ∧
      t'.queueNext = t0.queueNext := by
  have hInner : (queueNeighbourPatch st.objects tcb.queuePrev
      (queueUnlinkPredecessor tcb))[k]? = some (.tcb t0) := by
    rw [queueNeighbourPatch_at_other st.objects tcb.queuePrev _ hInv k hNe]; exact hk
  obtain ⟨t1, h1, hcase⟩ := queueNeighbourPatch_tcb_forward _ tcb.queueNext
    (queueUnlinkSuccessor tcb)
    (queueNeighbourPatch_invExt _ _ _ hInv) k t0 hInner
  refine ⟨t1, ?_, ?_⟩
  · rw [spliceOutMidQueueNode_eq_patches, hLookup]
    simp only
    exact h1
  · rcases hcase with rfl | rfl <;> rfl

/-- **WS-RR RR7.22 (residual)**: `removeFromAllEndpointQueues`'s fold body,
named.

Rewrites an endpoint only when one of its four queue boundaries names the swept
thread — the PR #831 write-set-honesty guard — and installs the two
`removeThreadFromQueue` results when it does.  Both queue rewrites read the
**spliced** pre-state, not the accumulator, so the value installed at a key does
not depend on the fold's iteration order. -/
def endpointSweepBody (stSpliced : SystemState) (tid : SeLe4n.ThreadId)
    (acc : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject) : SystemState :=
  match obj with
  | .endpoint _ =>
      match acc.getEndpointWitnessed? oid with
      | some ⟨ep, hEp⟩ =>
        if ep.sendQ.head == some tid || ep.sendQ.tail == some tid
            || ep.receiveQ.head == some tid || ep.receiveQ.tail == some tid then
          let ep' : Endpoint := (ep.withSendQ (removeThreadFromQueue stSpliced ep.sendQ tid)).withReceiveQ (removeThreadFromQueue stSpliced ep.receiveQ tid)
          acc.rewriteObject oid (.endpoint ep') (SystemState.rewriteAdmissible_endpoint hEp ep')
        else acc
      | none => acc
  | _ => acc

/-- **WS-RR RR7.22 (residual)**: the sweep *is* the fold of that body.

`rfl`, deliberately: this is the pin that keeps the named body and the
operation's own from diverging.  AN4-G.5's earlier `epFold` intermediate broke
because a proof matched the body **syntactically**; a definitional equation
fails the build instead. -/
theorem removeFromAllEndpointQueues_eq_fold (st : SystemState) (tid : SeLe4n.ThreadId) :
    removeFromAllEndpointQueues st tid =
      (spliceOutMidQueueNode st tid).objects.fold (spliceOutMidQueueNode st tid)
        (endpointSweepBody (spliceOutMidQueueNode st tid) tid) := rfl

/-- **WS-RR RR7.22 (residual)**: a thread sits at neither boundary of either of
an endpoint's queues.

The shape `queueHeadBlockedConsistent` and `endpointQueueTailBlockedConsistent`
read, collected once so the sweep's payoff and its consumers name the same
thing. -/
def threadOffQueueBoundaries (tid : SeLe4n.ThreadId) (ep : Endpoint) : Prop :=
  ep.sendQ.head ≠ some tid ∧ ep.sendQ.tail ≠ some tid ∧
  ep.receiveQ.head ≠ some tid ∧ ep.receiveQ.tail ≠ some tid

/-- **WS-RR RR7.22 (residual)**: `removeThreadFromQueue` is the identity on a
queue neither of whose boundaries names the thread — which is exactly the sweep
guard's negation, and so the reason the guard's two arms agree. -/
theorem removeThreadFromQueue_id_of_off_boundary (s : SystemState) (q : IntrusiveQueue)
    (tid : SeLe4n.ThreadId) (hH : q.head ≠ some tid) (hT : q.tail ≠ some tid) :
    removeThreadFromQueue s q tid = q := by
  unfold removeThreadFromQueue
  -- **WS-RR RR8.4**: the `some` arm is `queueRemoveBoundary` now, so the two
  -- boundary reads sit one definition deeper; the defensive arm keeps its own.
  cases lookupTcb s tid with
  | none => simp only [if_neg hH, if_neg hT]
  | some tcb => unfold queueRemoveBoundary; simp only [if_neg hH, if_neg hT]

/-- **WS-RR RR7.22 (residual)**: `removeThreadFromQueue` never leaves the removed
thread at a boundary.

The head advances to the thread's `queueNext` and the tail retreats to its
`queuePrev`, so the only way the result could still name it is a self-link —
which `tcbQueueChainAcyclic` forbids and which the two hypotheses state
directly.  The `lookupTcb`-absent branch clears both boundaries outright
(AN4-G.1's defensive clamp), so it needs no hypothesis at all. -/
theorem removeThreadFromQueue_off_boundary (s : SystemState) (q : IntrusiveQueue)
    (tid : SeLe4n.ThreadId)
    (hNext : ∀ tcb, lookupTcb s tid = some tcb → tcb.queueNext ≠ some tid)
    (hPrev : ∀ tcb, lookupTcb s tid = some tcb → tcb.queuePrev ≠ some tid) :
    (removeThreadFromQueue s q tid).head ≠ some tid ∧
      (removeThreadFromQueue s q tid).tail ≠ some tid := by
  unfold removeThreadFromQueue
  cases hT : lookupTcb s tid with
  | none => simp only; constructor <;> (split <;> simp_all)
  | some tcb =>
    -- **WS-RR RR8.4**: as above — the boundary reads are `queueRemoveBoundary`'s.
    unfold queueRemoveBoundary
    simp only
    constructor
    · split
      · exact hNext tcb hT
      · assumption
    · split
      · exact hPrev tcb hT
      · assumption

/-- **WS-RR RR7.22 (residual)**: after the sweep, every endpoint's two queues are
exactly `removeThreadFromQueue` of the ones it had — uniformly, whether the
guard fired or declined.

The declining arm is the interesting one: the guard's negation says no boundary
names the swept thread, which is precisely when `removeThreadFromQueue` is the
identity, so "rewritten" and "left alone" agree there. -/
theorem removeFromAllEndpointQueues_endpoint_value (st : SystemState) (tid : SeLe4n.ThreadId)
    (hExt : (spliceOutMidQueueNode st tid).objects.invExt)
    (k : SeLe4n.ObjId) (ep0 : Endpoint)
    (hEp0 : (spliceOutMidQueueNode st tid).objects[k]? = some (.endpoint ep0)) :
    ((removeFromAllEndpointQueues st tid).objects.invExt) ∧
      ∀ ep, (removeFromAllEndpointQueues st tid).objects[k]? = some (.endpoint ep) →
        ep.sendQ = removeThreadFromQueue (spliceOutMidQueueNode st tid) ep0.sendQ tid ∧
        ep.receiveQ = removeThreadFromQueue (spliceOutMidQueueNode st tid) ep0.receiveQ tid := by
  rw [removeFromAllEndpointQueues_eq_fold]
  refine RHTable.fold_pointwise (spliceOutMidQueueNode st tid).objects
    (spliceOutMidQueueNode st tid) (endpointSweepBody (spliceOutMidQueueNode st tid) tid)
    (Pre := fun o acc => acc.objects.invExt ∧
      acc.objects[o]? = (spliceOutMidQueueNode st tid).objects[o]?)
    (Q := fun o acc => acc.objects.invExt ∧
      ∀ e, acc.objects[o]? = some (.endpoint e) →
        ∀ e0, (spliceOutMidQueueNode st tid).objects[o]? = some (.endpoint e0) →
          e.sendQ = removeThreadFromQueue (spliceOutMidQueueNode st tid) e0.sendQ tid ∧
          e.receiveQ = removeThreadFromQueue (spliceOutMidQueueNode st tid) e0.receiveQ tid)
    hExt ?_ ?_ ?_ ?_ k (.endpoint ep0) hEp0 |>.imp id (fun h e he => h e he ep0 hEp0)
  · exact fun _ => ⟨hExt, rfl⟩
  · rintro acc o o' v' hne ⟨hE, hA⟩
    unfold endpointSweepBody
    cases v' with
    | endpoint ep =>
      simp only
      split
      · split
        · exact ⟨SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hE, by
            show (acc.rewriteObject o' _ _).objects[o]? = _
            rw [SystemState.rewriteObject_objects_ne acc o' o _ _ (fun h => hne h.symm) hE]
            exact hA⟩
        · exact ⟨hE, hA⟩
      · exact ⟨hE, hA⟩
    | _ => exact ⟨hE, hA⟩
  · rintro acc o v hGet ⟨hE, hA⟩
    unfold endpointSweepBody
    cases v with
    | endpoint ep =>
      simp only
      -- At the visit the accumulator still holds the enumerated record (`Pre`),
      -- so the witnessed lookup answers it and the body's own match reduces.
      have hAccEp : acc.getEndpoint? o = some ep :=
        (SystemState.getEndpoint?_eq_some_iff acc o ep).mpr (hA.trans hGet)
      simp only [SystemState.getEndpointWitnessed?_eq_some hAccEp]
      split
      · refine ⟨SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hE, ?_⟩
        intro e he e0 he0
        have he' := (SystemState.rewriteObject_objects_self acc o _ _ hE).symm.trans he
        obtain rfl := KernelObject.endpoint.inj (Option.some.inj he')
        have hGet' : (spliceOutMidQueueNode st tid).objects[o]?
            = some (KernelObject.endpoint ep) := hGet
        rw [he0] at hGet'
        obtain rfl : e0 = ep := KernelObject.endpoint.inj (Option.some.inj hGet')
        exact ⟨by simp, by simp⟩
      · refine ⟨hE, ?_⟩
        intro e he e0 he0
        rw [hA, he0] at he
        obtain rfl : e0 = e := KernelObject.endpoint.inj (Option.some.inj he)
        have hGet' : (spliceOutMidQueueNode st tid).objects[o]?
            = some (KernelObject.endpoint ep) := hGet
        rw [he0] at hGet'
        obtain rfl : e0 = ep := KernelObject.endpoint.inj (Option.some.inj hGet')
        rename_i hGuard
        simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hGuard
        exact ⟨(removeThreadFromQueue_id_of_off_boundary _ _ tid hGuard.1.1.1 hGuard.1.1.2).symm,
          (removeThreadFromQueue_id_of_off_boundary _ _ tid hGuard.1.2 hGuard.2).symm⟩
    | _ =>
      refine ⟨hE, ?_⟩
      intro e he e0 he0
      rw [hA, he0] at he
      exact absurd (hGet.symm.trans he0) (by simp)
  · rintro acc o o' v' hne ⟨hE, hQ⟩
    unfold endpointSweepBody
    cases v' with
    | endpoint ep =>
      simp only
      split
      · split
        · refine ⟨SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hE, ?_⟩
          intro e he
          have he' := (SystemState.rewriteObject_objects_ne acc o' o _ _
            (fun h => hne h.symm) hE).symm.trans he
          exact hQ e he'
        · exact ⟨hE, hQ⟩
      · exact ⟨hE, hQ⟩
    | _ => exact ⟨hE, hQ⟩

/-- **WS-RR RR7.22 (residual)**: the sweep's headline consequence — **no endpoint
still names the swept thread at a queue boundary**.

A corollary of the value description rather than a second fold argument: the
queues are `removeThreadFromQueue` outputs, and those never name the removed
thread at a boundary. -/
theorem removeFromAllEndpointQueues_off_boundary
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hExt : (spliceOutMidQueueNode st tid).objects.invExt)
    (hNext : ∀ tcb, lookupTcb (spliceOutMidQueueNode st tid) tid = some tcb →
      tcb.queueNext ≠ some tid)
    (hPrev : ∀ tcb, lookupTcb (spliceOutMidQueueNode st tid) tid = some tcb →
      tcb.queuePrev ≠ some tid)
    (oid : SeLe4n.ObjId) (ep0 : Endpoint)
    (hEp0 : (spliceOutMidQueueNode st tid).objects[oid]? = some (.endpoint ep0)) :
    ((removeFromAllEndpointQueues st tid).objects.invExt) ∧
      ∀ ep, (removeFromAllEndpointQueues st tid).objects[oid]? = some (.endpoint ep) →
        threadOffQueueBoundaries tid ep := by
  obtain ⟨hInv2, hVal⟩ := removeFromAllEndpointQueues_endpoint_value st tid hExt oid ep0 hEp0
  refine ⟨hInv2, fun ep hep => ?_⟩
  obtain ⟨hS, hR⟩ := hVal ep hep
  obtain ⟨h1, h2⟩ := removeThreadFromQueue_off_boundary (spliceOutMidQueueNode st tid)
    ep0.sendQ tid hNext hPrev
  obtain ⟨h3, h4⟩ := removeThreadFromQueue_off_boundary (spliceOutMidQueueNode st tid)
    ep0.receiveQ tid hNext hPrev
  exact ⟨by rw [hS]; exact h1, by rw [hS]; exact h2, by rw [hR]; exact h3, by rw [hR]; exact h4⟩


/-- **WS-RR RR7.22 (residual)**: the endpoint sweep writes only endpoints, so
every TCB survives it verbatim. -/
theorem removeFromAllEndpointQueues_tcb_frame (st : SystemState) (tid : SeLe4n.ThreadId)
    (hExt : (spliceOutMidQueueNode st tid).objects.invExt)
    (k : SeLe4n.ObjId) (t0 : TCB)
    (h : (spliceOutMidQueueNode st tid).objects[k]? = some (.tcb t0)) :
    (removeFromAllEndpointQueues st tid).objects[k]? = some (.tcb t0) := by
  rw [removeFromAllEndpointQueues_eq_fold]
  exact (RHTable.fold_preserves_of_lookup (spliceOutMidQueueNode st tid).objects
    (spliceOutMidQueueNode st tid) (endpointSweepBody (spliceOutMidQueueNode st tid) tid)
    (fun acc => acc.objects.invExt ∧ acc.objects[k]? = some (.tcb t0)) hExt ⟨hExt, h⟩
    (by
      rintro acc k' v' hGet ⟨hE, hA⟩
      unfold endpointSweepBody
      cases v' with
      | endpoint ep =>
        simp only
        split
        · split
          · have hNe : k' ≠ k := by
              intro hEq
              have h2 : (spliceOutMidQueueNode st tid).objects.get? k'
                  = some (KernelObject.endpoint ep) := hGet
              rw [hEq] at h2
              have h3 : (spliceOutMidQueueNode st tid).objects.get? k
                  = some (KernelObject.tcb t0) := h
              rw [h3] at h2
              cases h2
            refine ⟨SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hE, ?_⟩
            show (acc.rewriteObject k' _ _).objects[k]? = _
            rw [SystemState.rewriteObject_objects_ne acc k' k _ _ hNe hE]
            exact hA
          · exact ⟨hE, hA⟩
        · exact ⟨hE, hA⟩
      | _ => exact ⟨hE, hA⟩)).2

/-- **WS-RR RR7.22 (residual)**: a TCB reading after the sweep is the one the
sweep started from — the converse of the frame above, and what a conjunct stated
over the post-state needs to reach back. -/
theorem removeFromAllEndpointQueues_tcb_source (st : SystemState) (tid : SeLe4n.ThreadId)
    (hExt : (spliceOutMidQueueNode st tid).objects.invExt)
    (k : SeLe4n.ObjId) (t' : TCB)
    (h : (removeFromAllEndpointQueues st tid).objects[k]? = some (.tcb t')) :
    (spliceOutMidQueueNode st tid).objects[k]? = some (.tcb t') := by
  rw [removeFromAllEndpointQueues_eq_fold] at h
  refine ((RHTable.fold_preserves_of_lookup (spliceOutMidQueueNode st tid).objects
    (spliceOutMidQueueNode st tid) (endpointSweepBody (spliceOutMidQueueNode st tid) tid)
    (fun acc => acc.objects.invExt ∧ ∀ t, acc.objects[k]? = some (.tcb t) →
      (spliceOutMidQueueNode st tid).objects[k]? = some (.tcb t)) hExt
    ⟨hExt, fun _ ht => ht⟩ ?_).2 t' h)
  rintro acc k' v' hGet ⟨hE, hA⟩
  unfold endpointSweepBody
  cases v' with
  | endpoint ep' =>
    simp only
    split
    · split
      · refine ⟨SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hE, ?_⟩
        intro t ht
        by_cases hK : k' = k
        · subst hK
          have ht' := (SystemState.rewriteObject_objects_self acc k' _ _ hE).symm.trans ht
          cases ht'
        · have ht' := (SystemState.rewriteObject_objects_ne acc k' k _ _ hK hE).symm.trans ht
          exact hA t ht'
      · exact ⟨hE, hA⟩
    · exact ⟨hE, hA⟩
  | _ => exact ⟨hE, hA⟩

/-- **WS-RR RR7.22 (residual)**: an endpoint reading after the sweep had an
endpoint at the same key before it — the sweep invents no endpoints. -/
theorem removeFromAllEndpointQueues_endpoint_source (st : SystemState) (tid : SeLe4n.ThreadId)
    (hExt : (spliceOutMidQueueNode st tid).objects.invExt)
    (k : SeLe4n.ObjId) (ep : Endpoint)
    (h : (removeFromAllEndpointQueues st tid).objects[k]? = some (.endpoint ep)) :
    ∃ ep0, (spliceOutMidQueueNode st tid).objects[k]? = some (.endpoint ep0) := by
  rw [removeFromAllEndpointQueues_eq_fold] at h
  refine ((RHTable.fold_preserves_of_lookup (spliceOutMidQueueNode st tid).objects
    (spliceOutMidQueueNode st tid) (endpointSweepBody (spliceOutMidQueueNode st tid) tid)
    (fun acc => acc.objects.invExt ∧ ∀ e, acc.objects[k]? = some (.endpoint e) →
      ∃ e0, (spliceOutMidQueueNode st tid).objects[k]? = some (.endpoint e0)) hExt
    ⟨hExt, fun e he => ⟨e, he⟩⟩ ?_).2 ep h)
  rintro acc k' v' hGet ⟨hE, hA⟩
  unfold endpointSweepBody
  cases v' with
  | endpoint ep' =>
    simp only
    split
    · split
      · refine ⟨SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hE, ?_⟩
        intro e he
        by_cases hK : k' = k
        · subst hK
          exact ⟨ep', hGet⟩
        · have he' := (SystemState.rewriteObject_objects_ne acc k' k _ _ hK hE).symm.trans he
          exact hA e he'
      · exact ⟨hE, hA⟩
    · exact ⟨hE, hA⟩
  | _ => exact ⟨hE, hA⟩

end EndpointSweep

-- ============================================================================
-- WS-ZA ZA4.5: the donation arms as run-queue agreement stages
-- ============================================================================

/-- The replenishment migration writes two release queues and the contexts'
release fields: nothing the run-queue agreement reads. -/
theorem migrateSchedContextReplenishment_runQueueStage (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore : SeLe4n.Kernel.Concurrency.CoreId) :
    SystemState.RunQueueStage st (migrateSchedContextReplenishment st scId fromCore toCore) :=
  .of_releaseOnlyWrite (migrateSchedContextReplenishment_releaseOnlyWrite st scId fromCore toCore)
    (migrateSchedContextReplenishment_agree st scId fromCore toCore)
    (migrateSchedContextReplenishment_preserves_objects_invExt st scId fromCore toCore)
    (fun _ h => migrateSchedContextReplenishment_refined h scId fromCore toCore)
    (fun _ _ h s => migrateSchedContextReplenishment_refillsSoundExcept h scId fromCore toCore s)

/-- The donation hand-back rebinds a context and two threads' bindings: no run
queue, no placement field. -/
theorem returnDonatedSchedContext_runQueueStage {st st' : SystemState}
    {serverTid : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId}
    {originalOwner : SeLe4n.ThreadId} {newOwner? : Option SeLe4n.ThreadId}
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    SystemState.RunQueueStage st st' :=
  have hS := returnDonatedSchedContext_scheduler_eq st st' serverTid scId originalOwner
    newOwner? h
  SystemState.RunQueueStage.of_placement
    (fun hInv => returnDonatedSchedContext_preserves_objects_invExt st st' serverTid scId
      originalOwner hInv newOwner? h)
    (by rw [hS]) (by rw [hS])
    (fun hInv x => returnDonatedSchedContext_getTcb?_placement_eq st st' serverTid scId
      originalOwner hInv newOwner? h x)
    (fun hInv => SystemState.StateMono.of_stateFields
      (returnDonatedSchedContext_getTcb?_stateFields_eq st st' serverTid scId originalOwner
        hInv newOwner? h))
    (fun hInv => returnDonatedSchedContext_tableReferenceFrame hInv h)
    (fun hInv => returnDonatedSchedContext_releaseStateAgree hInv h)
    (fun hInv => returnDonatedSchedContext_refillViewsKept hInv h)
    (fun hInv => returnDonatedSchedContext_yieldLinksKept hInv h)
    (by rw [hS])
    (by rw [returnDonatedSchedContext_machine_eq st st' serverTid scId originalOwner newOwner? h])

theorem returnDonatedSchedContextResolved_runQueueStage {st st' : SystemState}
    {serverTid : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId}
    {originalOwner : SeLe4n.ThreadId}
    (h : returnDonatedSchedContextResolved st serverTid scId originalOwner = .ok st') :
    SystemState.RunQueueStage st st' :=
  let ⟨_, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose h
  returnDonatedSchedContext_runQueueStage hPop

theorem cleanupDonatedSchedContext_runQueueStage {st st' : SystemState}
    {tid : SeLe4n.ThreadId} (h : cleanupDonatedSchedContext st tid = .ok st') :
    SystemState.RunQueueStage st st' := by
  unfold cleanupDonatedSchedContext at h
  split at h
  · cases h; exact .refl st
  · split at h
    · exact returnDonatedSchedContextResolved_runQueueStage h
    · cases h; exact .refl st

/-- The migrating donation cancel: the hand-back, then the replenishment move. -/
theorem cancelDonatedDonationOnCore_runQueueStage {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} (h : cancelDonatedDonationOnCore st tid tcb = .ok st') :
    SystemState.RunQueueStage st st' := by
  unfold cancelDonatedDonationOnCore at h
  split at h
  · split at h
    · cases h
    · rename_i s1 h1
      cases h
      exact (cleanupDonatedSchedContext_runQueueStage h1).trans
        (migrateSchedContextReplenishment_runQueueStage _ _ _ _)
  · cases h

/-- The in-place unbind: a context write, two scheduler-side writes the
agreement does not read, the binding clear, and the key flags. -/
theorem cancelBoundDonationOnCore_runQueueStage {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB}
    (h : cancelBoundDonationOnCore st tid tcb = .ok st') :
    SystemState.RunQueueStage st st' := by
  unfold cancelBoundDonationOnCore at h
  split at h
  · rename_i scId _
    cases h
    have key : ∀ X : SystemState, SystemState.RunQueueStage st X →
        SystemState.RunQueueStage st (markKeyChangeFrom st
          (X.updateTcb tid fun tcb' => { tcb' with scBindingScCode := 0, scBindingOwnerCode := 0 }) tid) :=
      fun X hX => hX.trans ((SystemState.RunQueueStage.updateTcb X tid
        (f := fun tcb' => { tcb' with scBindingScCode := 0, scBindingOwnerCode := 0 }) (fun _ _ => rfl)).trans
        (markKeyChangeFrom_runQueueStage st _ tid))
    apply key
    have hU := SystemState.updateSchedContext_scheduler st scId
      (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })
    cases hG : st.getSchedContext? scId with
    | none =>
      rw [SystemState.updateSchedContext_eq_self_of_none hG]
      exact SchedContextOps.purgeReplenishment_runQueueStage _ _ (by rw [hG]; rfl)
    | some sc =>
      refine SchedContextOps.schedContextUnbind_stage_close hG rfl ?_ (fun hI a ha => ?_)
      · apply SystemState.RunQueueFrameStage.of_placement
        · exact fun hInv => SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv
        · show (st.updateSchedContext scId _).scheduler.runQueue = _
          rw [hU]
        · show (st.updateSchedContext scId _).scheduler.runQueueEnds = _
          rw [hU]
        · intro hInv x
          exact congrArg (Option.map TCB.placement)
            (SystemState.updateSchedContext_getTcb? st scId _ hInv x)
        · exact fun hInv => SystemState.StateMono.of_getTcb
            (SystemState.updateSchedContext_getTcb? st scId _ hInv)
        · exact SystemState.TableReferenceFrame.updateSchedContext st scId _
        · exact fun hInv => .updateSchedContext st scId _ hInv (fun _ => ⟨rfl, rfl, rfl⟩)
        · exact fun hInv => .updateSchedContext st scId _ hInv
        · exact fun hInv => Kernel.YieldLinksKept.updateSchedContext st scId _ hInv (fun _ => rfl)
        · show (st.updateSchedContext scId _).scheduler.currentCode = _
          rw [hU]
        · exact congrArg MachineState.residentCode (SystemState.updateSchedContext_machine st scId _)
      · rw [SystemState.updateSchedContext_getSchedContext?_self _ _ _ hI, hG] at ha
        cases ha; rfl
  · cases h

/-- The retype's donation arm: the identity, the in-place unbind, or the
migrating return. -/
theorem cancelDonationArmOnCore_runQueueStage {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} (h : cancelDonationArmOnCore st tid tcb = .ok st') :
    SystemState.RunQueueStage st st' := by
  unfold cancelDonationArmOnCore at h
  split at h
  · cases h; exact .refl st
  · exact cancelBoundDonationOnCore_runQueueStage h
  · exact cancelDonatedDonationOnCore_runQueueStage h

/-- The migrating donation cancel moves no thread's run-queue core: the
hand-back rewrites bindings and the migration writes replenish queues. -/
theorem cancelDonatedDonationOnCore_runCoresAgree {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} (hInv : st.objects.invExt)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st') : SystemState.RunCoresAgree st' st := by
  unfold cancelDonatedDonationOnCore at h
  split at h
  · split at h
    · cases h
    · rename_i s1 h1
      cases h
      exact SystemState.RunCoresAgree.trans
        (fun y => by rw [migrateSchedContextReplenishment_getTcb?])
        (cleanupDonatedSchedContext_runCoresAgree st s1 tid hInv h1)
  · cases h

/-- The in-place donation cancel moves no thread's run-queue core: a context
write, the binding clear and the key flags. -/
theorem cancelBoundDonationOnCore_runCoresAgree {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB}
    (hInv : st.objects.invExt) (h : cancelBoundDonationOnCore st tid tcb = .ok st') :
    SystemState.RunCoresAgree st' st := by
  unfold cancelBoundDonationOnCore at h
  split at h
  · rename_i scId _
    cases h
    have hInv1 := SystemState.updateSchedContext_preserves_objects_invExt st scId
      (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) hInv
    refine SystemState.RunCoresAgree.trans
      (SystemState.RunCoresAgree.of_objects (markKeyChangeFrom_objects _ _ _)) ?_
    refine SystemState.RunCoresAgree.trans
      (SystemState.updateTcb_runCoreCode _ tid _ (by intro _; rfl)
        (SchedContextOps.purgeReplenishment_objects_invExt _ _ hInv1)) ?_
    exact SystemState.RunCoresAgree.trans
      (s2 := st.updateSchedContext scId
          (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }))
      (fun y => by rw [SchedContextOps.purgeReplenishment_getTcb?])
      (fun y => by rw [SystemState.updateSchedContext_getTcb? _ _ _ hInv])
  · cases h

/-- The reservation arm moves no thread's run-queue core. -/
theorem cancelDonationArmOnCore_runCoresAgree {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} (hInv : st.objects.invExt)
    (h : cancelDonationArmOnCore st tid tcb = .ok st') : SystemState.RunCoresAgree st' st := by
  unfold cancelDonationArmOnCore at h
  split at h
  · cases h; exact SystemState.RunCoresAgree.refl _
  · exact cancelBoundDonationOnCore_runCoresAgree hInv h
  · exact cancelDonatedDonationOnCore_runCoresAgree hInv h

end SeLe4n.Kernel
