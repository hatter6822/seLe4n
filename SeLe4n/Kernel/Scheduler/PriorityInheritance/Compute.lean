-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.PriorityInheritance.BlockingGraph
import SeLe4n.Kernel.Scheduler.Operations.Selection
import SeLe4n.Kernel.Scheduler.RunQueueLinkFrame
import SeLe4n.Kernel.Scheduler.ReplyWaitersOps

namespace SeLe4n.Kernel.PriorityInheritance

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

-- ============================================================================
-- D4-F: computeMaxWaiterPriority
-- ============================================================================

/-- D4-F: Compute the maximum effective priority among all threads
directly blocked on `tid` via Reply IPC. Returns `none` if no waiters.

WS-RC R5.C (DEEP-SCH-02): uses the total `effectiveSchedParams` helper,
which falls back to the waiter's TCB priority/deadline/domain when SC
lookup fails (unreachable under `schedContextStoreConsistent`).  This is
part of R5.C's API-uniformity goal: callers no longer thread `Option`
propagation through the priority-inheritance fold.

WS-RC R5.C.1 (DEEP-SCH-02): The pre-R5 `effectivePriority` partial helper
that this site previously consumed has been RETIRED (see
`Selection.lean` Z4-B section). -/
def computeMaxWaiterPriority (st : SystemState) (tid : ThreadId)
    : Option Priority :=
  let waiters := waitersOf st tid
  waiters.foldl (fun acc waiterTid =>
    match st.getTcb? waiterTid with
    | some waiterTcb =>
      let (prio, _, _) := effectiveSchedParams st waiterTcb
      match acc with
      | none => some prio
      | some curMax => some ⟨Nat.max curMax.val prio.val⟩
    | none => acc) none

/-- D4-F: computeMaxWaiterPriority of a thread with no waiters is none. -/
theorem computeMaxWaiterPriority_no_waiters (st : SystemState) (tid : ThreadId)
    (h : waitersOf st tid = []) :
    computeMaxWaiterPriority st tid = none := by
  simp [computeMaxWaiterPriority, h, SystemState.getTcb?]

-- ============================================================================
-- WS-RC R5.B.2 / Phase P1: computeMaxWaiterPriority frame lemma
-- ============================================================================

/-- WS-RC R5.B.2 / Phase P1: `waitersOf` is invariant under an operation that
    preserves the object table.  This is the `objects`-frame for the waiter
    list; since WS-ZA ZA4.6 the list reads only reply views
    (`waitersOf_of_replyViews`). -/
theorem waitersOf_frame
    (st st' : SystemState) (tid : ThreadId)
    (hObjects : st'.objects = st.objects) :
    waitersOf st' tid = waitersOf st tid :=
  SystemState.replyWaitersOf_of_replyViews (by unfold SystemState.replyViews SystemState.getObject?; rw [hObjects]) tid

/-- WS-ZA ZA4.6: `waitersOf` reads reply views and nothing else. -/
theorem waitersOf_of_replyViews
    (st st' : SystemState) (tid : ThreadId)
    (hR : st'.replyViews = st.replyViews) :
    waitersOf st' tid = waitersOf st tid :=
  SystemState.replyWaitersOf_of_replyViews hR tid

/-- WS-RC R5.B.2 / Phase P1: `getSchedContext?` is invariant under an
    operation that preserves the object table. -/
theorem getSchedContext?_frame
    (st st' : SystemState) (scId : SchedContextId)
    (hObjects : st'.objects = st.objects) :
    st'.getSchedContext? scId = st.getSchedContext? scId :=
  -- The fact is stated once, beside the accessor it is about
  -- (`Model/State.lean`); this is the namespace-local spelling the liveness
  -- suite's `#check` anchor names, not a second proof of it.
  SystemState.getSchedContext?_frame hObjects scId

/-- WS-RC R5.B.2 / Phase P1: `effectiveSchedParams` is invariant under an
    operation that preserves the object table.  The helper reads only
    `tcb` fields (passed by value) and `st.getSchedContext?` which reads
    `st.objects` exclusively. -/
theorem effectiveSchedParams_frame
    (st st' : SystemState) (tcb : TCB)
    (hObjects : st'.objects = st.objects) :
    effectiveSchedParams st' tcb = effectiveSchedParams st tcb := by
  unfold effectiveSchedParams
  -- The two sides differ only at the `st'.getSchedContext?` / `st.getSchedContext?`
  -- read; for unbound the result is fully determined by tcb fields.
  split
  · rfl  -- unbound: no SC lookup
  · rename_i scId _
    rw [getSchedContext?_frame st st' scId hObjects]
  · rename_i scId _ _
    rw [getSchedContext?_frame st st' scId hObjects]

/-- Helper for `computeMaxWaiterPriority_frame`: a pointwise-equal closure
    produces equal folds.  Used after the waiter list is shown equal.

    We use a definitionally-equal closure that pins the accumulator type
    to `Option Priority`, avoiding type-inference failures in the
    inductive body. -/
private def cmwpFoldBody (st : SystemState)
    (acc : Option SeLe4n.Priority) (waiterTid : ThreadId)
    : Option SeLe4n.Priority :=
  match st.getTcb? waiterTid with
  | some waiterTcb =>
    let (prio, _, _) := effectiveSchedParams st waiterTcb
    match acc with
    | none => some prio
    | some curMax => some ⟨Nat.max curMax.val prio.val⟩
  | none => acc

/-- Helper: `cmwpFoldBody st'` agrees with `cmwpFoldBody st` pointwise when
    `st'.objects = st.objects`. -/
private theorem cmwpFoldBody_frame
    (st st' : SystemState)
    (hObjects : st'.objects = st.objects)
    (acc : Option SeLe4n.Priority) (waiterTid : ThreadId) :
    cmwpFoldBody st' acc waiterTid = cmwpFoldBody st acc waiterTid := by
  unfold cmwpFoldBody
  rw [SystemState.getTcb?_frame hObjects]
  cases hObj : st.getTcb? waiterTid with
  | none => rfl
  | some tc => simp only [effectiveSchedParams_frame st st' tc hObjects]

private theorem computeMaxWaiterPriority_foldBody_frame
    (st st' : SystemState) (ws : List ThreadId)
    (hObjects : st'.objects = st.objects) :
    ∀ acc : Option SeLe4n.Priority,
      ws.foldl (cmwpFoldBody st') acc = ws.foldl (cmwpFoldBody st) acc := by
  induction ws with
  | nil => intro acc; rfl
  | cons head tail ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [cmwpFoldBody_frame st st' hObjects acc head]
    exact ih _

/-- Bridge: `computeMaxWaiterPriority` is the `cmwpFoldBody` fold. -/
private theorem computeMaxWaiterPriority_eq_cmwpFoldBody (st : SystemState) (tid : ThreadId) :
    computeMaxWaiterPriority st tid = (waitersOf st tid).foldl (cmwpFoldBody st) none := by
  rfl

/-! WS-ZA ZA4.6: **the maximum as compiled.**  `computeMaxWaiterPriority` folds
the waiter list; the compiled form walks the server's reply-waiter queue by its
link codes and keeps the running maximum as a code (`0` for none, `p + 1` for
priority `p`), so it builds neither the list nor an `Option` per waiter, and
reads each TCB through `objectEntry?`, which allocates nothing. -/

/-- The walk of at most `n` waiters from the one code `c` names, folding each
waiter's effective priority into the maximum code `acc`. -/
def maxWaiterCode (st : SystemState) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | n + 1, c, acc =>
    if c = 0 then acc else
    match st.objectEntry? (⟨c - 1⟩ : ThreadId).toObjId with
    | some e => match e.value with
      | .tcb t => maxWaiterCode st n t.replyWaiterNextCode (Nat.max acc (t.boostedPriority.val + 1))
      | _ => acc
    | none => acc

/-- WS-ZA ZA4.7: the maximum waiter priority as its code
(`SeLe4n.Priority.optCode`), the form the boost write stores in
`TCB.pipBoostCode`, so the boost never builds the optional priority. -/
def computeMaxWaiterCode (st : SystemState) (tid : ThreadId) : Nat :=
  match st.objectEntry? tid.toObjId with
  | some e => match e.value with
    | .tcb ts => maxWaiterCode st ts.replyWaitersCount ts.replyWaitersHeadCode 0
    | _ => 0
  | none => 0

/-- WS-ZA ZA4.6: the compiled `computeMaxWaiterPriority` (see above). -/
@[inline] def computeMaxWaiterPriorityImpl (st : SystemState) (tid : ThreadId) :
    Option SeLe4n.Priority :=
  SeLe4n.Priority.ofOptCode (computeMaxWaiterCode st tid)

/-- A TCB read through `objectEntry?` is the `getTcb?` read. -/
private theorem objectEntry?_tcb_match (st : SystemState) (tid : ThreadId) {α : Sort _}
    (f : TCB → α) (d : α) :
    (match st.objectEntry? tid.toObjId with
      | some e => match e.value with
        | .tcb t => f t
        | _ => d
      | none => d) = (match st.getTcb? tid with
        | some t => f t
        | none => d) := by
  unfold SystemState.getTcb?
  rw [SystemState.objects_get?_eq_objectEntry?]
  cases st.objectEntry? tid.toObjId with
  | none => rfl
  | some e => cases h : e.value <;> simp [h]

private theorem cmwpFoldBody_code (st : SystemState) (a : Nat) (w : ThreadId) (t : TCB)
    (h : st.getTcb? w = some t) :
    cmwpFoldBody st (SeLe4n.Priority.ofOptCode a) w =
      SeLe4n.Priority.ofOptCode (Nat.max a (t.boostedPriority.val + 1)) := by
  unfold cmwpFoldBody
  rw [h]
  simp only []
  rw [show (effectiveSchedParams st t) = ((effectiveSchedParams st t).1,
      (effectiveSchedParams st t).2) from rfl, effectiveSchedParams_fst_eq_boostedPriority]
  cases a with
  | zero => simp [SeLe4n.Priority.ofOptCode]
  | succ k => simp [SeLe4n.Priority.ofOptCode, Nat.succ_max_succ]

private theorem maxWaiterCode_eq_fold (st : SystemState) :
    ∀ (n : Nat) (cur : Option ThreadId) (a : Nat),
      (st.replyWaitersWalk n cur).foldl (cmwpFoldBody st) (SeLe4n.Priority.ofOptCode a) =
        SeLe4n.Priority.ofOptCode (maxWaiterCode st n (ThreadId.optCode cur) a)
  | 0, _, _ => rfl
  | _ + 1, none, _ => rfl
  | n + 1, some w, a => by
    simp only [SystemState.replyWaitersWalk, List.foldl_cons, maxWaiterCode, ThreadId.optCode,
      Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    have hE := objectEntry?_tcb_match st w
      (fun t => maxWaiterCode st n t.replyWaiterNextCode (Nat.max a (t.boostedPriority.val + 1))) a
    simp only [] at hE
    rw [show (⟨w.val⟩ : ThreadId) = w from rfl, hE]
    cases hT : st.getTcb? w with
    | none =>
      simp only [Option.bind_none]
      unfold cmwpFoldBody; rw [hT]
      cases n <;> rfl
    | some t =>
      simp only [Option.bind_some]
      rw [cmwpFoldBody_code st a w t hT, maxWaiterCode_eq_fold st n t.replyWaiterNext]
      simp only [TCB.replyWaiterNext, SeLe4n.ThreadId.optCode_ofOptCode]

@[csimp] theorem computeMaxWaiterPriority_eq_impl :
    @computeMaxWaiterPriority = @computeMaxWaiterPriorityImpl := by
  funext st tid
  rw [computeMaxWaiterPriority_eq_cmwpFoldBody]
  unfold computeMaxWaiterPriorityImpl computeMaxWaiterCode
  have hE := objectEntry?_tcb_match st tid
    (fun ts => maxWaiterCode st ts.replyWaitersCount ts.replyWaitersHeadCode 0) 0
  simp only [] at hE
  rw [hE]
  unfold waitersOf SystemState.replyWaitersOf
  cases st.getTcb? tid with
  | none => rfl
  | some ts =>
    simp only []
    rw [show (none : Option SeLe4n.Priority) = SeLe4n.Priority.ofOptCode 0 from rfl,
      maxWaiterCode_eq_fold]
    simp only [TCB.replyWaitersHead, SeLe4n.ThreadId.optCode_ofOptCode]


/-- The boost's stored code is the walk's code. -/
theorem optCode_computeMaxWaiterPriority (st : SystemState) (tid : ThreadId) :
    SeLe4n.Priority.optCode (computeMaxWaiterPriority st tid) = computeMaxWaiterCode st tid := by
  rw [show computeMaxWaiterPriority st tid = computeMaxWaiterPriorityImpl st tid from
    congrFun (congrFun computeMaxWaiterPriority_eq_impl st) tid]
  exact SeLe4n.Priority.optCode_ofOptCode _

/-- WS-RC R5.B.2 / Phase P1: `computeMaxWaiterPriority` is invariant under
    an operation that preserves the object table.

    This is the simplest "full frame": when the objects table is unchanged,
    every read site of `computeMaxWaiterPriority` (waitersOf,
    effectiveSchedParams via `st.getSchedContext?`) returns identical
    results, so the fold collapses to the pre-state value.

    Used by `ensureRunnable_preserves_computeMaxWaiterPriority` and
    `schedule_preserves_computeMaxWaiterPriority` (Phase Q2), both of
    which only modify `scheduler.runQueue` or `machine.regs` /
    `tcb.registerContext` — fields not read by `computeMaxWaiterPriority`. -/
theorem computeMaxWaiterPriority_frame
    (st st' : SystemState) (tid : ThreadId)
    (hObjects : st'.objects = st.objects) :
    computeMaxWaiterPriority st' tid = computeMaxWaiterPriority st tid := by
  -- Both reads (`waitersOf` and the fold body) only touch `st.objects`; if it
  -- agrees across `st` and `st'`, the results agree.
  rw [computeMaxWaiterPriority_eq_cmwpFoldBody, computeMaxWaiterPriority_eq_cmwpFoldBody,
      waitersOf_frame st st' tid hObjects]
  exact computeMaxWaiterPriority_foldBody_frame st st' (waitersOf st tid) hObjects none

/-! WS-ZA ZA4.5: the same reads across a step that writes only run-queue
links.  A waiter's blocking edge, its priority, deadline, domain and binding are
none of them run-queue fields, so every read agrees.  `objectsAgreeOffRunLinks`
also leaves reply-waiter links free (WS-ZA ZA4.6), which the waiter list reads,
so the step's caller states that the reply views agree (`hR`). -/

private theorem cmwpFoldBody_of_objectsAgreeOffRunLinks
    (st st' : SystemState) (h : st'.objectsAgreeOffRunLinks st)
    (acc : Option SeLe4n.Priority) (waiterTid : ThreadId) :
    cmwpFoldBody st' acc waiterTid = cmwpFoldBody st acc waiterTid := by
  unfold cmwpFoldBody
  cases e : st.getTcb? waiterTid with
  | none =>
    have hn : st'.getTcb? waiterTid = none := by
      have := h.getTcb?_isSome waiterTid
      rw [e] at this
      exact Option.not_isSome_iff_eq_none.mp (by rw [this]; decide)
    rw [hn]
  | some tc =>
    obtain ⟨tc', _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht', rfl⟩ :=
      h.get_tcb_fwd ((SystemState.getTcb?_eq_some_iff st waiterTid tc).mp e)
    rw [(SystemState.getTcb?_eq_some_iff st' waiterTid tc').mpr ht']
    simp only [effectiveSchedParams_of_objectsAgreeOffRunLinks st st' _ h]
    rfl

theorem computeMaxWaiterPriority_of_objectsAgreeOffRunLinks
    (st st' : SystemState) (tid : ThreadId) (h : st'.objectsAgreeOffRunLinks st)
    (hR : st'.replyViews = st.replyViews) :
    computeMaxWaiterPriority st' tid = computeMaxWaiterPriority st tid := by
  rw [computeMaxWaiterPriority_eq_cmwpFoldBody, computeMaxWaiterPriority_eq_cmwpFoldBody,
      waitersOf_of_replyViews st st' tid hR]
  generalize (none : Option SeLe4n.Priority) = acc
  induction (waitersOf st tid) generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [cmwpFoldBody_of_objectsAgreeOffRunLinks st st' h acc hd]
    exact ih _

theorem blockingServer_of_objectsAgreeOffRunLinks
    (st st' : SystemState) (t : ThreadId) (h : st'.objectsAgreeOffRunLinks st) :
    blockingServer st' t = blockingServer st t := by
  unfold blockingServer
  cases e : st.getTcb? t with
  | none =>
    have hn : st'.getTcb? t = none := by
      have := h.getTcb?_isSome t
      rw [e] at this
      exact Option.not_isSome_iff_eq_none.mp (by rw [this]; decide)
    rw [hn]
  | some tc =>
    obtain ⟨tc', _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht', rfl⟩ :=
      h.get_tcb_fwd ((SystemState.getTcb?_eq_some_iff st t tc).mp e)
    rw [(SystemState.getTcb?_eq_some_iff st' t tc').mpr ht']; rfl

-- ============================================================================
-- WS-RC R5.B.2 / Phase P1: Per-field frame for computeMaxWaiterPriority
-- ============================================================================
--
-- `computeMaxWaiterPriority` reads from `objects`.  The fields it actually
-- consumes from each TCB are:
--   * the reply view (`TCB.replyView`, via `waitersOf`, which walks the
--     server's reply-waiter queue).
--   * `priority`, `deadline`, `domain`, `pipBoost`, `schedContextBinding`
--     (via `effectiveSchedParams` for the waiter's scheduling params).
-- And from each SchedContext (via `effectiveSchedParams`):
--   * `priority`, `deadline`, `domain`.
--
-- A finer-grained frame: if an operation rewrites one TCB at `oid` such
-- that the new TCB agrees with the old one on every field above, then
-- `computeMaxWaiterPriority` is invariant.  This is the framing used by
-- `schedule_preserves_computeMaxWaiterPriority` (Phase Q2), where the
-- only modification is to `registerContext`.

/-- WS-RC R5.B.2 / Phase P1: A TCB-only rewrite at `oid` that preserves
    every field read by `effectiveSchedParams`/`waitersOf` preserves
    `effectiveSchedParams` for any TCB.  Specifically: if the new TCB at
    `oid` shares `(priority, deadline, domain, pipBoost, schedContextBinding)`
    with the old one, and SCs are unchanged, then `effectiveSchedParams`
    on any TCB is invariant. -/
theorem effectiveSchedParams_frame_per_field
    (st st' : SystemState) (tcb : TCB)
    (hSc : ∀ scId, st'.getSchedContext? scId = st.getSchedContext? scId) :
    effectiveSchedParams st' tcb = effectiveSchedParams st tcb := by
  unfold effectiveSchedParams
  split
  · rfl
  · rename_i scId _
    rw [hSc scId]
  · rename_i scId _ _
    rw [hSc scId]

-- ============================================================================
-- WS-RC R5.B.2 / Phase P1: Per-field frame for waitersOf
-- ============================================================================

/-- The per-slot equivalence we need to frame `waitersOf` and
    `computeMaxWaiterPriority`.  An object lookup at `objId` is either:
    - Identical in both states, or
    - A TCB rewrite preserving every field read by `waitersOf` and
      `effectiveSchedParams` (i.e., the reply view,
      `schedContextBinding`, `priority`, `deadline`, `domain`,
      `pipBoost`).

    This captures the schedule-induced frame where one TCB's
    `registerContext` (NOT read by `waitersOf`/`effectiveSchedParams`)
    may have been rewritten. -/
def computeMaxWaiterPriority_lookup_equiv
    (st st' : SystemState) (objId : ObjId) : Prop :=
  st'.objects[objId]? = st.objects[objId]? ∨
  ∃ tcb tcb',
    st.objects[objId]? = some (.tcb tcb) ∧
    st'.objects[objId]? = some (.tcb tcb') ∧
    tcb'.replyView = tcb.replyView ∧
    tcb'.schedContextBinding = tcb.schedContextBinding ∧
    tcb'.priority = tcb.priority ∧
    tcb'.deadline = tcb.deadline ∧
    tcb'.domain = tcb.domain ∧
    tcb'.pipBoost = tcb.pipBoost

theorem waitersOf_frame_per_field
    (st st' : SystemState) (tid : ThreadId)
    (hEquiv : ∀ objId, computeMaxWaiterPriority_lookup_equiv st st' objId) :
    waitersOf st' tid = waitersOf st tid := by
  refine waitersOf_of_replyViews st st' tid (funext fun k => ?_)
  unfold SystemState.replyViews SystemState.getObject?
  rcases hEquiv k with hSame | ⟨tcb, tcb', hPre, hPost, hView, _⟩
  · rw [hSame]
  · rw [hPre, hPost, objReplyView_tcb, objReplyView_tcb, hView]

/-- Helper: pointwise-equal closures produce equal `cmwpFoldBody` folds
    under the per-field equivalence frame.  This is the inductive
    workhorse for `computeMaxWaiterPriority_frame_per_field`. -/
private theorem cmwpFoldBody_frame_per_field
    (st st' : SystemState) (ws : List ThreadId)
    (hEquiv : ∀ objId, computeMaxWaiterPriority_lookup_equiv st st' objId)
    (hSc : ∀ scId, st'.getSchedContext? scId = st.getSchedContext? scId) :
    ∀ acc : Option SeLe4n.Priority,
      ws.foldl (cmwpFoldBody st') acc = ws.foldl (cmwpFoldBody st) acc := by
  induction ws with
  | nil => intro acc; rfl
  | cons head tail ih =>
    intro acc
    simp only [List.foldl_cons]
    have hStep : cmwpFoldBody st' acc head = cmwpFoldBody st acc head := by
      unfold cmwpFoldBody
      rcases hEquiv head.toObjId with hSame | ⟨tcb, tcb', hPre, hPost, _, hBind, hPrio, hDl, hDom, hPip⟩
      · rw [SystemState.getTcb?_congr_at hSame]
        -- After rewriting, both sides have same discriminant.  The inner bodies
        -- differ on effectiveSchedParams st' vs st.  Bridge via frame_per_field.
        cases hLook : st.getTcb? head with
        | none => rfl
        | some waiterTcb =>
          simp only
          rw [effectiveSchedParams_frame_per_field st st' waiterTcb hSc]
      · have hPreA : st.getTcb? head = some tcb := by
          unfold SystemState.getTcb?; rw [hPre]
        have hPostA : st'.getTcb? head = some tcb' := by
          unfold SystemState.getTcb?; rw [hPost]
        rw [hPreA, hPostA]
        -- After rw, both sides have `match some (.tcb tcb') with ...` and
        -- `match some (.tcb tcb) with ...`.  Reduce both matches via simp.
        simp only
        -- Now goal is `effectiveSchedParams st' tcb' = effectiveSchedParams st tcb`.
        -- Show this by transitivity through `effectiveSchedParams st tcb'`.
        have hESP : effectiveSchedParams st' tcb' = effectiveSchedParams st tcb := by
          have h1 : effectiveSchedParams st' tcb' = effectiveSchedParams st tcb' :=
            effectiveSchedParams_frame_per_field st st' tcb' hSc
          have h2 : effectiveSchedParams st tcb' = effectiveSchedParams st tcb := by
            unfold effectiveSchedParams
            -- The boost is applied through `TCB.boostedPriority` /
            -- `Priority.raisedBy` since `v0.35.28`; both are transparent to
            -- `simp`, so the per-field facts still close this.
            simp only [TCB.boostedPriority_eq, Priority.raisedBy,
              hBind, hPip, hPrio, hDl, hDom]
          exact h1.trans h2
        rw [hESP]
    rw [hStep]
    exact ih _

/-- WS-RC R5.B.2 / Phase P1: `computeMaxWaiterPriority` is invariant
    under a per-slot lookup-equivalence frame.

    For each `objId`, the lookup either is unchanged or is a TCB rewrite
    preserving every field read by `waitersOf` (the reply view) and
    by `effectiveSchedParams` (`schedContextBinding`, `priority`,
    `deadline`, `domain`, `pipBoost`).  Together with `getSchedContext?`
    preservation, this implies
    `computeMaxWaiterPriority` is preserved.

    Used by `schedule_preserves_computeMaxWaiterPriority` (Phase Q2):
    `schedule` may rewrite one TCB's `registerContext` (NOT read by
    `computeMaxWaiterPriority`), so the per-field frame applies. -/
theorem computeMaxWaiterPriority_frame_per_field
    (st st' : SystemState) (tid : ThreadId)
    (hEquiv : ∀ objId, computeMaxWaiterPriority_lookup_equiv st st' objId)
    (hSc : ∀ scId, st'.getSchedContext? scId = st.getSchedContext? scId) :
    computeMaxWaiterPriority st' tid = computeMaxWaiterPriority st tid := by
  rw [computeMaxWaiterPriority_eq_cmwpFoldBody, computeMaxWaiterPriority_eq_cmwpFoldBody,
      waitersOf_frame_per_field st st' tid hEquiv]
  exact cmwpFoldBody_frame_per_field st st' (waitersOf st tid) hEquiv hSc none

-- ============================================================================
-- WS-SM SM5.F.1: computeMaxWaiterPriorityOnCore (per-core waiter slice)
-- ============================================================================
--
-- The PIP blocking graph is *global*: a thread `w` on core `cᵥ` can be blocked
-- (`.blockedOnReply _ (some tid)`) on a holder `tid` running on a *different*
-- core `c_h`.  The boost a holder *inherits* is therefore the max over ALL its
-- waiters regardless of core — `computeMaxWaiterPriority` (above) is the value a
-- correct PIP must apply, and under-boosting (taking only some cores' waiters)
-- would re-introduce priority inversion.  `computeMaxWaiterPriorityOnCore` is the
-- per-core *analytic slice* of that max — the contribution of the waiters whose
-- home core (`determineTargetCore`) is `c`.  It is NOT the boost value (the boost
-- is global); it is the decomposition used by `pipBoost_perCore_consistent`
-- (SM5.F.3) to bound a single core's contribution, and by the cross-core wake to
-- reason about which cores' schedulers must be poked.

/-- WS-SM SM5.F.1 (plan §3.6): the numeric value of an optional priority, with
`none` (no waiters) reading as `0`.  Used to state the per-core ≤ global
decomposition and the `pipBoost_perCore_consistent` bound without `Option`
gymnastics. -/
def optPriorityVal (o : Option SeLe4n.Priority) : Nat :=
  o.elim 0 (·.val)

@[simp] theorem optPriorityVal_none : optPriorityVal none = 0 := rfl

@[simp] theorem optPriorityVal_some (p : SeLe4n.Priority) :
    optPriorityVal (some p) = p.val := rfl

/-- WS-SM SM5.F.1 (plan §3.6): compute the maximum effective priority among the
threads directly blocked on `tid` via Reply IPC **whose home core is `c`**
(`determineTargetCore st w = c`).  Returns `none` if `tid` has no on-core
waiters.

This is the per-core analogue of `computeMaxWaiterPriority`, restricted to the
waiters that core `c` is responsible for.  It is a pure *analytic* quantity: the
PIP boost actually applied to a holder is the **global** `computeMaxWaiterPriority`
(`updatePipBoostOnCore` sets exactly that — only the run-queue *bucket migration*
is per-core), so this slice is bounded above by the global value
(`computeMaxWaiterPriorityOnCore_le_global`) and never used to *set* a boost
(that would under-boost and re-introduce inversion).

**Slice-membership deviation from the plan (WS-SM SM5.F.1).**  The plan §3.6 sketch
partitions waiters by run-queue membership (`w ∈ runQueueOnCore c`).  This
implementation instead partitions by the waiter's *home* core
(`determineTargetCore st w == c`, its `cpuAffinity`).  The home-core partition is the
*correct* one for the decomposition: it is a genuine partition of the waiter set
(every waiter has exactly one home core — `computeMaxWaiterPriority_eq_sup_perCore`
relies on this totality + disjointness), whereas run-queue membership is not a
partition (a waiter is *blocked*, hence in **no** run queue — `blockedOn*NotRunnable`
— so the run-queue sketch would slice every waiter into the empty set and lose the
entire boost).  A PIP *waiter* is by definition blocked-on-reply, so its run-queue
slot is empty; its *home* core is what determines which core's scheduler must be
poked when the holder it is waiting on is boosted.  The home-core partition is
therefore both well-defined and operationally meaningful, and the plan's run-queue
phrasing is corrected to it here. -/
def computeMaxWaiterPriorityOnCore (st : SystemState) (c : CoreId) (tid : ThreadId)
    : Option Priority :=
  let waiters := waitersOf st tid
  waiters.foldl (fun acc waiterTid =>
    if SeLe4n.Kernel.determineTargetCore st waiterTid == c then
      match st.getTcb? waiterTid with
      | some waiterTcb =>
        let (prio, _, _) := effectiveSchedParams st waiterTcb
        match acc with
        | none => some prio
        | some curMax => some ⟨Nat.max curMax.val prio.val⟩
      | none => acc
    else acc) none

/-- WS-SM SM5.F.1: per-core fold body, factored to relate `computeMaxWaiterPriorityOnCore`
to the global `cmwpFoldBody`.  On-core waiters are processed exactly as
`cmwpFoldBody`; off-core waiters leave the accumulator untouched. -/
private def cmwpFoldBodyOnCore (st : SystemState) (c : CoreId)
    (acc : Option SeLe4n.Priority) (waiterTid : ThreadId)
    : Option SeLe4n.Priority :=
  if SeLe4n.Kernel.determineTargetCore st waiterTid == c then
    cmwpFoldBody st acc waiterTid
  else acc

/-- WS-SM SM5.F.1: `computeMaxWaiterPriorityOnCore` is the `cmwpFoldBodyOnCore` fold. -/
private theorem computeMaxWaiterPriorityOnCore_eq_foldBody
    (st : SystemState) (c : CoreId) (tid : ThreadId) :
    computeMaxWaiterPriorityOnCore st c tid
      = (waitersOf st tid).foldl (cmwpFoldBodyOnCore st c) none := by
  rfl

/-- WS-SM SM5.F.1: `computeMaxWaiterPriorityOnCore` has no on-core waiters ⇒ `none`. -/
theorem computeMaxWaiterPriorityOnCore_no_waiters (st : SystemState) (c : CoreId)
    (tid : ThreadId) (h : waitersOf st tid = []) :
    computeMaxWaiterPriorityOnCore st c tid = none := by
  simp [computeMaxWaiterPriorityOnCore, h, SystemState.getTcb?]

/-- WS-SM SM5.F.1: a waiter's effective-priority contribution to the fold (`0` for
a non-TCB).  Phrased via the typed `getTcb?` accessor — `cmwpFoldBody`'s raw
`objects[w]?` read is bridged to this once in `cmwpFoldBody_optPriorityVal`. -/
private def waiterContrib (st : SystemState) (w : ThreadId) : Nat :=
  match st.getTcb? w with
  | some t => (effectiveSchedParams st t).1.val
  | none => 0

/-- WS-SM SM5.F.1: the value of one global fold step is `max` of the running
value and the waiter's effective-priority contribution. -/
private theorem cmwpFoldBody_optPriorityVal (st : SystemState)
    (acc : Option SeLe4n.Priority) (w : ThreadId) :
    optPriorityVal (cmwpFoldBody st acc w)
      = Nat.max (optPriorityVal acc) (waiterContrib st w) := by
  unfold cmwpFoldBody waiterContrib SystemState.getTcb?
  cases hObj : st.objects[w.toObjId]? with
  | none => simp [optPriorityVal]
  | some obj =>
    cases obj with
    | tcb t =>
      cases acc with
      | none => simp [optPriorityVal]
      | some m => simp [optPriorityVal]
    | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
      | schedContext _ | reply _ | frame _ | pageTable _ => simp [optPriorityVal]

/-- WS-SM SM5.F.1: one per-core fold step never exceeds the corresponding global
step (it either matches it, on-core, or leaves the accumulator unchanged). -/
private theorem cmwpFoldBodyOnCore_optPriorityVal_le (st : SystemState) (c : CoreId)
    (acc : Option SeLe4n.Priority) (w : ThreadId) :
    optPriorityVal (cmwpFoldBodyOnCore st c acc w)
      ≤ Nat.max (optPriorityVal acc) (waiterContrib st w) := by
  unfold cmwpFoldBodyOnCore
  split
  · -- on-core: equals the global step
    exact Nat.le_of_eq (cmwpFoldBody_optPriorityVal st acc w)
  · -- off-core: accumulator unchanged ≤ max with anything
    exact Nat.le_max_left _ _

/-- WS-SM SM5.F.1 (decomposition workhorse): a per-core fold from `a` is bounded by
the global fold from `b` whenever `a`'s value is bounded by `b`'s.  Proved by
induction on the waiter list, using the per-step bound. -/
private theorem foldBody_onCore_le_global (st : SystemState) (c : CoreId)
    (ws : List ThreadId) :
    ∀ a b : Option SeLe4n.Priority, optPriorityVal a ≤ optPriorityVal b →
      optPriorityVal (ws.foldl (cmwpFoldBodyOnCore st c) a)
        ≤ optPriorityVal (ws.foldl (cmwpFoldBody st) b) := by
  induction ws with
  | nil => intro a b hab; simpa using hab
  | cons head tail ih =>
    intro a b hab
    simp only [List.foldl_cons]
    apply ih
    -- per-step: value(perCoreBody a head) ≤ value(globalBody b head)
    rw [cmwpFoldBody_optPriorityVal]
    refine Nat.le_trans (cmwpFoldBodyOnCore_optPriorityVal_le st c a head) ?_
    exact Nat.max_le.mpr ⟨Nat.le_trans hab (Nat.le_max_left _ _), Nat.le_max_right _ _⟩

/-- WS-SM SM5.F.1 (plan §3.6): **per-core ≤ global decomposition.**  The per-core
waiter slice never exceeds the global max-waiter priority.  This is the core
soundness fact: a single core's contribution to a holder's inherited priority is
bounded by the (global) boost the holder actually receives.  It is what makes
`pipBoost_perCore_consistent` (SM5.F.3) sound. -/
theorem computeMaxWaiterPriorityOnCore_le_global (st : SystemState) (c : CoreId)
    (tid : ThreadId) :
    optPriorityVal (computeMaxWaiterPriorityOnCore st c tid)
      ≤ optPriorityVal (computeMaxWaiterPriority st tid) := by
  rw [computeMaxWaiterPriorityOnCore_eq_foldBody, computeMaxWaiterPriority_eq_cmwpFoldBody]
  exact foldBody_onCore_le_global st c (waitersOf st tid) none none (Nat.le_refl 0)

/-- WS-SM SM5.F.1: one per-core fold step is invariant under an object-table-
preserving operation — `determineTargetCore`, the object lookup, and
`effectiveSchedParams` all read only `objects`. -/
private theorem cmwpFoldBodyOnCore_frame (st st' : SystemState) (c : CoreId)
    (hObjects : st'.objects = st.objects)
    (acc : Option SeLe4n.Priority) (w : ThreadId) :
    cmwpFoldBodyOnCore st' c acc w = cmwpFoldBodyOnCore st c acc w := by
  unfold cmwpFoldBodyOnCore
  have hDtc : SeLe4n.Kernel.determineTargetCore st' w = SeLe4n.Kernel.determineTargetCore st w := by
    unfold SeLe4n.Kernel.determineTargetCore SystemState.getTcb?; rw [hObjects]
  rw [hDtc, cmwpFoldBody_frame st st' hObjects acc w]

/-- WS-SM SM5.F.1: pointwise-equal per-core fold bodies produce equal folds. -/
private theorem cmwpFoldBodyOnCore_fold_frame (st st' : SystemState) (c : CoreId)
    (ws : List ThreadId) (hObjects : st'.objects = st.objects) :
    ∀ acc : Option SeLe4n.Priority,
      ws.foldl (cmwpFoldBodyOnCore st' c) acc = ws.foldl (cmwpFoldBodyOnCore st c) acc := by
  induction ws with
  | nil => intro acc; rfl
  | cons head tail ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [cmwpFoldBodyOnCore_frame st st' c hObjects acc head]
    exact ih _

/-- WS-SM SM5.F.1: `computeMaxWaiterPriorityOnCore` is invariant under an operation
that preserves the object table — every read site
(`waitersOf`, `determineTargetCore`, `effectiveSchedParams`) depends only on
`objects`.  The per-core analogue of `computeMaxWaiterPriority_frame`. -/
theorem computeMaxWaiterPriorityOnCore_frame
    (st st' : SystemState) (c : CoreId) (tid : ThreadId)
    (hObjects : st'.objects = st.objects) :
    computeMaxWaiterPriorityOnCore st' c tid = computeMaxWaiterPriorityOnCore st c tid := by
  rw [computeMaxWaiterPriorityOnCore_eq_foldBody, computeMaxWaiterPriorityOnCore_eq_foldBody,
      waitersOf_frame st st' tid hObjects]
  exact cmwpFoldBodyOnCore_fold_frame st st' c (waitersOf st tid) hObjects none

-- ============================================================================
-- WS-SM SM5.F.1 (plan §3.6): full per-core decomposition (completeness)
-- ============================================================================
--
-- `computeMaxWaiterPriorityOnCore_le_global` (above) proves each per-core slice
-- never *exceeds* the global boost — the soundness direction (a core's
-- contribution cannot over-claim).  The *completeness* direction below proves the
-- global boost equals the **maximum over every core's slice**: no waiter's
-- contribution is lost when the global max-waiter priority is reassembled from the
-- per-core slices.  Together they give the exact decomposition
--   global  =  sup_{c ∈ allCores} (slice c)
-- which justifies the cross-core wake's "poke every core whose slice rose" policy:
-- iterating `allCores` and poking each core with a positive slice covers the
-- entire boost, and pokes no spurious core.

-- Generic `Nat.max`-foldl helpers (core-Lean; no Mathlib).  A fold of the shape
-- `l.foldl (fun n a => Nat.max n (f a)) s` is the running supremum of `f` over `l`
-- seeded at `s`.

private theorem start_le_foldl_maxf {α : Type _} (f : α → Nat) :
    ∀ (l : List α) (s : Nat), s ≤ l.foldl (fun n a => Nat.max n (f a)) s := by
  intro l
  induction l with
  | nil => intro s; exact Nat.le_refl _
  | cons head tail ih =>
    intro s
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left s (f head)) (ih _)

private theorem le_foldl_maxf {α : Type _} (f : α → Nat) :
    ∀ (l : List α) (s : Nat) (a : α), a ∈ l →
      f a ≤ l.foldl (fun n x => Nat.max n (f x)) s := by
  intro l
  induction l with
  | nil => intro s a ha; simp at ha
  | cons head tail _ih =>
    intro s a ha
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ha with hEq | hTail
    · subst hEq
      exact Nat.le_trans (Nat.le_max_right s (f a)) (start_le_foldl_maxf f tail _)
    · exact _ih _ a hTail

private theorem foldl_maxf_le_of_all {α : Type _} (f : α → Nat) :
    ∀ (l : List α) (B s : Nat), s ≤ B → (∀ a ∈ l, f a ≤ B) →
      l.foldl (fun n a => Nat.max n (f a)) s ≤ B := by
  intro l
  induction l with
  | nil => intro B s hs _; simpa using hs
  | cons head tail ih =>
    intro B s hs hf
    simp only [List.foldl_cons]
    apply ih
    · exact Nat.max_le.mpr ⟨hs, hf head List.mem_cons_self⟩
    · intro a ha; exact hf a (List.mem_cons_of_mem head ha)

/-- WS-SM SM5.F.1: `optPriorityVal` of the global max-waiter fold is the running
supremum of each waiter's effective-priority contribution (`waiterContrib`). -/
private theorem cmwpFold_optPriorityVal (st : SystemState) :
    ∀ (ws : List ThreadId) (acc : Option SeLe4n.Priority),
      optPriorityVal (ws.foldl (cmwpFoldBody st) acc)
        = ws.foldl (fun n w => Nat.max n (waiterContrib st w)) (optPriorityVal acc) := by
  intro ws
  induction ws with
  | nil => intro acc; rfl
  | cons head tail ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih (cmwpFoldBody st acc head), cmwpFoldBody_optPriorityVal st acc head]

/-- WS-SM SM5.F.1: per-core fold body in numeric `optPriorityVal` form — an on-core
waiter contributes its `waiterContrib`; an off-core waiter is skipped. -/
private def sliceBody (st : SystemState) (c : CoreId) (n : Nat) (w : ThreadId) : Nat :=
  if SeLe4n.Kernel.determineTargetCore st w == c then Nat.max n (waiterContrib st w) else n

/-- WS-SM SM5.F.1: at an on-core waiter the slice body is a `max` step. -/
private theorem sliceBody_of_home (st : SystemState) (c : CoreId) (n : Nat) (w : ThreadId)
    (h : SeLe4n.Kernel.determineTargetCore st w = c) :
    sliceBody st c n w = Nat.max n (waiterContrib st w) := by
  unfold sliceBody
  rw [h]
  simp

/-- WS-SM SM5.F.1: `optPriorityVal` of the per-core slice fold is the running
supremum of `waiterContrib` restricted to on-core waiters. -/
private theorem cmwpFoldOnCore_optPriorityVal (st : SystemState) (c : CoreId) :
    ∀ (ws : List ThreadId) (acc : Option SeLe4n.Priority),
      optPriorityVal (ws.foldl (cmwpFoldBodyOnCore st c) acc)
        = ws.foldl (sliceBody st c) (optPriorityVal acc) := by
  intro ws
  induction ws with
  | nil => intro acc; rfl
  | cons head tail ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih (cmwpFoldBodyOnCore st c acc head)]
    congr 1
    unfold cmwpFoldBodyOnCore sliceBody
    split
    · exact cmwpFoldBody_optPriorityVal st acc head
    · rfl

/-- WS-SM SM5.F.1: closed numeric form of the global max-waiter priority. -/
theorem computeMaxWaiterPriority_value (st : SystemState) (tid : ThreadId) :
    optPriorityVal (computeMaxWaiterPriority st tid)
      = (waitersOf st tid).foldl (fun n w => Nat.max n (waiterContrib st w)) 0 := by
  rw [computeMaxWaiterPriority_eq_cmwpFoldBody, cmwpFold_optPriorityVal]
  simp only [optPriorityVal_none]

/-- WS-SM SM5.F.1: closed numeric form of the per-core max-waiter slice. -/
theorem computeMaxWaiterPriorityOnCore_value (st : SystemState) (c : CoreId) (tid : ThreadId) :
    optPriorityVal (computeMaxWaiterPriorityOnCore st c tid)
      = (waitersOf st tid).foldl (sliceBody st c) 0 := by
  rw [computeMaxWaiterPriorityOnCore_eq_foldBody, cmwpFoldOnCore_optPriorityVal]
  simp only [optPriorityVal_none]

-- Monotonicity + membership lemmas for the per-core slice fold.

private theorem sliceBody_mono (st : SystemState) (c : CoreId) (w : ThreadId) {n n' : Nat}
    (h : n ≤ n') : sliceBody st c n w ≤ sliceBody st c n' w := by
  unfold sliceBody
  split
  · exact Nat.max_le.mpr ⟨Nat.le_trans h (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
  · exact h

private theorem start_le_foldl_sliceBody (st : SystemState) (c : CoreId) :
    ∀ (l : List ThreadId) (s : Nat), s ≤ l.foldl (sliceBody st c) s := by
  intro l
  induction l with
  | nil => intro s; exact Nat.le_refl _
  | cons head tail ih =>
    intro s
    simp only [List.foldl_cons]
    refine Nat.le_trans ?_ (ih (sliceBody st c s head))
    unfold sliceBody
    split
    · exact Nat.le_max_left _ _
    · exact Nat.le_refl _

/-- WS-SM SM5.F.1: an on-core waiter's contribution is captured by its core's
slice fold — the per-waiter capture lemma underpinning the completeness
direction. -/
private theorem waiterContrib_le_foldl_sliceBody (st : SystemState) (c : CoreId) :
    ∀ (l : List ThreadId) (s : Nat) (w : ThreadId),
      w ∈ l → SeLe4n.Kernel.determineTargetCore st w = c →
      waiterContrib st w ≤ l.foldl (sliceBody st c) s := by
  intro l
  induction l with
  | nil => intro s w hw _; simp at hw
  | cons head tail ih =>
    intro s w hw hHome
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hw with hEq | hTail
    · subst hEq
      refine Nat.le_trans ?_ (start_le_foldl_sliceBody st c tail (sliceBody st c s w))
      rw [sliceBody_of_home st c s w hHome]
      exact Nat.le_max_right _ _
    · exact ih _ w hTail hHome

/-- WS-SM SM5.F.1 (plan §3.6): **exact per-core decomposition.**  The global
max-waiter priority equals the supremum over every core of that core's waiter
slice.  Combined with `computeMaxWaiterPriorityOnCore_le_global` (each slice ≤
global, soundness) this is the *completeness* half: iterating `allCores` and
taking the slice maximum reconstructs the full boost, losing no waiter's
contribution.  This is the formal justification that the cross-core wake's
per-core poke policy covers the entire inherited priority. -/
theorem computeMaxWaiterPriority_eq_sup_perCore (st : SystemState) (tid : ThreadId) :
    optPriorityVal (computeMaxWaiterPriority st tid)
      = SeLe4n.Kernel.Concurrency.allCores.foldl
          (fun n c => Nat.max n (optPriorityVal (computeMaxWaiterPriorityOnCore st c tid))) 0 := by
  apply Nat.le_antisymm
  · -- global ≤ sup over cores: each waiter is captured by its home core's slice
    rw [computeMaxWaiterPriority_value]
    apply foldl_maxf_le_of_all (waiterContrib st) (waitersOf st tid)
    · exact Nat.zero_le _
    · intro w hw
      have hHome : SeLe4n.Kernel.determineTargetCore st w
          ∈ SeLe4n.Kernel.Concurrency.allCores := by
        unfold SeLe4n.Kernel.Concurrency.allCores
        exact List.mem_finRange _
      have h1 : waiterContrib st w
          ≤ optPriorityVal (computeMaxWaiterPriorityOnCore st
              (SeLe4n.Kernel.determineTargetCore st w) tid) := by
        rw [computeMaxWaiterPriorityOnCore_value]
        exact waiterContrib_le_foldl_sliceBody st _ (waitersOf st tid) 0 w hw rfl
      exact Nat.le_trans h1
        (le_foldl_maxf (fun c => optPriorityVal (computeMaxWaiterPriorityOnCore st c tid))
          SeLe4n.Kernel.Concurrency.allCores 0 _ hHome)
  · -- sup over cores ≤ global: each slice ≤ global (soundness, already proven)
    apply foldl_maxf_le_of_all
        (fun c => optPriorityVal (computeMaxWaiterPriorityOnCore st c tid))
        SeLe4n.Kernel.Concurrency.allCores
    · exact Nat.zero_le _
    · intro c _
      exact computeMaxWaiterPriorityOnCore_le_global st c tid

end SeLe4n.Kernel.PriorityInheritance
