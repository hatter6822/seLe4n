-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.Defs
import SeLe4n.Kernel.IPC.Invariant.PerCore

/-!
# WS-SM SM6.D — Per-core IPC structural invariant bundle

This module is the definitional layer of SM6.D (plan
`docs/planning/SMP_CROSS_CORE_IPC_PLAN.md` §3.3 / §5 "SM6.D"): it restricts
the full IPC invariant bundle (`ipcInvariantFull`, twenty conjuncts at the
time of landing — the plan's "15 conjuncts post-R4" grew by five during the
SM6.D reply-object hardening) to **per-core views** parameterised by an
explicit `(c : CoreId)`.

## Restriction discipline

Following plan §3.3 ("each `_perCore` variant restricts to threads on a
specific core, via the `cpuAffinity` field"), a conjunct whose *subject* is
a thread (the TCB whose property the conjunct asserts) is restricted to the
threads **homed** on core `c` — where a thread's home core is its
`cpuAffinity`, defaulting to `bootCoreId` for an unpinned thread, exactly
the core the operational wake path targets (`determineTargetCore`; the
coherence lemma `determineTargetCore_eq_threadHomeCore` lives with the
preservation layer).  Three kinds of clause are deliberately **not**
restricted:

* **Shared-object clauses** (`ipcInvariant` — notification queue
  well-formedness, `badgeWellFormed`, the per-endpoint
  `dualQueueEndpointWellFormed` clause, the endpoint head-disjointness
  clause): endpoints, notifications and CNodes are shared kernel objects
  with no core affinity; every core's view carries the whole obligation,
  because every core can operate on the object.  Restricting them via
  queue-member affinity would *weaken* the bundle (a core would admit an
  ill-formed shared object as long as no local thread is enqueued on it).
* **Existence-asserting object clauses** (the backward
  `replyCallerLinkageReciprocal` clause: `reply.caller = some tid` ⇒ the
  TCB *exists* and reciprocates): the subject is the Reply object; the
  clause asserts the very existence of the TCB, so there is no TCB whose
  affinity could scope it without losing the ∀-core recovery direction.
* **Witness positions** (the `prev` thread witnessing queue reachability,
  the donation `owner`, the second thread of a uniqueness pair): witnesses
  are part of the asserted property, not the quantification domain.

This makes the decomposition **exact**: the ∀-core aggregate
(`ipcInvariantFull_smp`) is equivalent to the global bundle plus the
`∀ c` slices of the one scheduler-reading conjunct
(`ipcInvariantFull_smp_iff_full_and_passive_smp`) — instantiating each
restricted conjunct at the subject's own home core recovers the global
form, and the global form weakens to every slice.  Nothing is lost and
nothing is silently strengthened.

The one scheduler-reading conjunct, `passiveServerIdle`, uses the
established SM4.D per-core form `passiveServerIdle_perCore`
(`IPC/Invariant/PerCore.lean`), which parameterises the scheduler *reads*
(`runQueueOnCore c` / `currentOnCore c`) rather than the thread domain.

**AK7 typed-accessor discipline** (matching SM4.D): every per-core
predicate routes TCB / Reply / SchedContext lookups through the typed
`getTcb?` / `getReply?` / `getSchedContext?` accessors (zero new
`tid`-keyed raw-lookup sites); endpoint / notification lookups keep the
raw `objects[oid]?` form (`ObjId`-keyed, outside `RAW_LOOKUP_TID`) so the
bodies stay textually parallel to the single-core surface.

Axiom-clean: every theorem depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §0  Home core
-- ============================================================================

/-- WS-SM SM6.D: the core a thread is *homed* on — its `cpuAffinity`, with
an unpinned thread (`cpuAffinity = none`) homed on `bootCoreId`.  This is
the definitional counterpart of the operational wake target
`determineTargetCore` (which reads the same field through `getTcb?`); the
coherence lemma `determineTargetCore_eq_threadHomeCore` (preservation
layer) pins the two together, so the per-core invariant slices partition
threads by exactly the core the cross-core wake path delivers them to. -/
def threadHomeCore (tcb : TCB) : CoreId :=
  tcb.cpuAffinity.getD bootCoreId

-- ============================================================================
-- §1  Per-core structural conjunct forms (SM6.D.3–D.6 + companions)
-- ============================================================================

/-- SM6.D.3: per-core form of `ipcStateQueueMembershipConsistent` (V3-J
reachability).  Every thread homed on core `c` that is blocked on an
endpoint is reachable from that endpoint's corresponding queue head via
the TCB linkage chain.  The reachability witness (`prev`) is *not*
affinity-restricted: queue interiors may interleave threads homed on
different cores. -/
def ipcStateQueueMembershipConsistent_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.getTcb? tid = some tcb →
    threadHomeCore tcb = c →
    match tcb.ipcState with
    | .blockedOnSend epId =>
        ∃ ep, st.objects[epId]? = some (KernelObject.endpoint ep) ∧
          (ep.sendQ.head = some tid ∨
           ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
             st.getTcb? prev = some prevTcb ∧
             TCB.queueNext prevTcb = some tid)
    | .blockedOnReceive epId =>
        ∃ ep, st.objects[epId]? = some (KernelObject.endpoint ep) ∧
          (ep.receiveQ.head = some tid ∨
           ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
             st.getTcb? prev = some prevTcb ∧
             TCB.queueNext prevTcb = some tid)
    | .blockedOnCall epId =>
        ∃ ep, st.objects[epId]? = some (KernelObject.endpoint ep) ∧
          (ep.sendQ.head = some tid ∨
           ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
             st.getTcb? prev = some prevTcb ∧
             TCB.queueNext prevTcb = some tid)
    | _ => True

/-- SM6.D.4: per-core form of `endpointQueueNoDup` (V3-K).  The self-loop
prohibition is restricted to threads homed on core `c`; the head
disjointness clause is a shared-object property of the endpoint itself and
is carried whole in every core's view. -/
def endpointQueueNoDup_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (ep : Endpoint),
    st.objects[oid]? = some (.endpoint ep) →
    (∀ (tid : SeLe4n.ThreadId) (tcb : TCB), st.getTcb? tid = some tcb →
      threadHomeCore tcb = c → TCB.queueNext tcb ≠ some tid) ∧
    (ep.sendQ.head = none ∨ ep.receiveQ.head = none ∨
     ep.sendQ.head ≠ ep.receiveQ.head)

/-- SM6.D.5: per-core form of `queueNextBlockingConsistent` (V3-J-cross).
Restricted on the link *source* `a` (every `queueNext` link is owned by
the thread it leaves from); the target `b` is a witness position. -/
def queueNextBlockingConsistent_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (a b : SeLe4n.ThreadId) (tcbA tcbB : TCB),
    st.getTcb? a = some tcbA → threadHomeCore tcbA = c →
    st.getTcb? b = some tcbB →
    tcbA.queueNext = some b →
    queueNextBlockingMatch tcbA.ipcState tcbB.ipcState

/-- SM6.D.6: per-core form of `queueHeadBlockedConsistent` (V3-J-head).
Restricted on the *head thread* (the subject whose blocking state the
conjunct pins); the endpoint is a shared object. -/
def queueHeadBlockedConsistent_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (epId : SeLe4n.ObjId) (ep : Endpoint) (hd : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[epId]? = some (.endpoint ep) →
    st.getTcb? hd = some tcb → threadHomeCore tcb = c →
    (ep.receiveQ.head = some hd → tcb.ipcState = .blockedOnReceive epId) ∧
    (ep.sendQ.head = some hd →
      tcb.ipcState = .blockedOnSend epId ∨ tcb.ipcState = .blockedOnCall epId)

/-- SM6.D: per-core form of `tcbQueueLinkIntegrity` (WS-H5/C-04).  Forward
integrity restricted on the link source `a`; reverse integrity restricted
on the back-link source `b`. -/
def tcbQueueLinkIntegrity_perCore (st : SystemState) (c : CoreId) : Prop :=
  (∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
    st.getTcb? a = some tcbA → threadHomeCore tcbA = c →
    ∀ (b : SeLe4n.ThreadId), tcbA.queueNext = some b →
      ∃ tcbB, st.getTcb? b = some tcbB ∧ tcbB.queuePrev = some a) ∧
  (∀ (b : SeLe4n.ThreadId) (tcbB : TCB),
    st.getTcb? b = some tcbB → threadHomeCore tcbB = c →
    ∀ (a : SeLe4n.ThreadId), tcbB.queuePrev = some a →
      ∃ tcbA, st.getTcb? a = some tcbA ∧ tcbA.queueNext = some b)

/-- SM6.D: per-core form of `tcbQueueChainAcyclic` (WS-H5 / AN5-B).  No
thread homed on core `c` reaches itself via `queueNext`.  The ∀-core
aggregate recovers the global form because every cycle starts at *some*
thread, whose TCB the cycle's first edge exhibits
(`QueueNextPath.firstEdge`). -/
def tcbQueueChainAcyclic_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.getTcb? tid = some tcb → threadHomeCore tcb = c →
    ¬ QueueNextPath st tid tid

/-- SM6.D: per-core form of `dualQueueSystemInvariant` (WS-H5).  The
per-endpoint dual-queue well-formedness clause asserts head/tail TCB
*existence* on a shared object and is carried whole; the two system-wide
TCB-link clauses restrict to threads homed on core `c`. -/
def dualQueueSystemInvariant_perCore (st : SystemState) (c : CoreId) : Prop :=
  (∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
    st.objects[epId]? = some (.endpoint ep) →
    dualQueueEndpointWellFormed epId st) ∧
  tcbQueueLinkIntegrity_perCore st c ∧
  tcbQueueChainAcyclic_perCore st c

/-- SM6.D: per-core form of `allPendingMessagesBounded` (WS-H12d/A-09). -/
def allPendingMessagesBounded_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (msg : IpcMessage),
    st.getTcb? tid = some tcb → threadHomeCore tcb = c →
    tcb.pendingMessage = some msg →
    msg.bounded

/-- SM6.D: per-core form of `waitingThreadsPendingMessageNone` (V3-G1). -/
def waitingThreadsPendingMessageNone_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.getTcb? tid = some tcb → threadHomeCore tcb = c →
    match tcb.ipcState with
    | .blockedOnReceive _ => tcb.pendingMessage = none
    | .blockedOnNotification _ => tcb.pendingMessage = none
    | _ => True

/-- SM6.D: per-core form of `blockedThreadTimeoutConsistent` (Z6-J).  The
referenced SchedContext lookup routes through the typed
`getSchedContext?`. -/
def blockedThreadTimeoutConsistent_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId),
    st.getTcb? tid = some tcb → threadHomeCore tcb = c →
    tcb.timeoutBudget = some scId →
    (∃ sc, st.getSchedContext? scId = some sc) ∧
    (match tcb.ipcState with
     | .blockedOnSend _ | .blockedOnReceive _ | .blockedOnCall _ | .blockedOnReply _ _ => True
     | _ => False)

/-- SM6.D: per-core form of `donationChainAcyclic` (Z7-F).  Restricted on
the first thread of the 2-cycle; the ∀-core aggregate recovers the global
form at that thread's home core. -/
def donationChainAcyclic_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid1 tid2 : SeLe4n.ThreadId) (tcb1 tcb2 : TCB)
    (scId1 scId2 : SeLe4n.SchedContextId),
    st.getTcb? tid1 = some tcb1 → threadHomeCore tcb1 = c →
    st.getTcb? tid2 = some tcb2 →
    tcb1.schedContextBinding = .donated scId1 tid2 →
    tcb2.schedContextBinding = .donated scId2 tid1 →
    False

/-- SM6.D: per-core form of `donationOwnerValid` (Z7-G).  Restricted on
the donee (the thread holding the `.donated` binding); the SchedContext
and the original owner are witness positions.  The SchedContext lookup
routes through the typed `getSchedContext?`, the owner through
`getTcb?`. -/
def donationOwnerValid_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId),
    st.getTcb? tid = some tcb → threadHomeCore tcb = c →
    tcb.schedContextBinding = .donated scId owner →
    (∃ sc, st.getSchedContext? scId = some sc ∧
      sc.boundThread = some tid) ∧
    (∃ ownerTcb, st.getTcb? owner = some ownerTcb ∧
      ownerTcb.schedContextBinding = .unbound ∧
      ∃ epId replyTarget, ownerTcb.ipcState = .blockedOnReply epId replyTarget)

/-- SM6.D: per-core form of `donationBudgetTransfer` (Z7-I).  Restricted on
the first holder of the uniqueness pair. -/
def donationBudgetTransfer_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid1 tid2 : SeLe4n.ThreadId) (tcb1 tcb2 : TCB)
    (scId : SeLe4n.SchedContextId),
    st.getTcb? tid1 = some tcb1 → threadHomeCore tcb1 = c →
    st.getTcb? tid2 = some tcb2 →
    tid1 ≠ tid2 →
    tcb1.schedContextBinding.scId? = some scId →
    tcb2.schedContextBinding.scId? = some scId →
    False

/-- SM6.D: per-core form of `blockedOnReplyHasTarget` (AJ1-B / M-04). -/
def blockedOnReplyHasTarget_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (endpointId : SeLe4n.ObjId)
    (replyTarget : Option SeLe4n.ThreadId),
    st.getTcb? tid = some tcb → threadHomeCore tcb = c →
    tcb.ipcState = .blockedOnReply endpointId replyTarget →
    replyTarget.isSome

/-- SM6.D: per-core form of `replyCallerLinkageReciprocal`.  The forward
clause (TCB → Reply) restricts on the TCB subject; the backward clause
(Reply → TCB) asserts the very *existence* of the caller TCB — its subject
is the Reply object, which has no affinity — so it is carried whole in
every core's view (restricting it on the asserted TCB's affinity would be
circular and would lose the ∀-core recovery). -/
def replyCallerLinkageReciprocal_perCore (st : SystemState) (c : CoreId) : Prop :=
  (∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (rid : SeLe4n.ReplyId),
      st.getTcb? tid = some tcb → threadHomeCore tcb = c →
      tcb.replyObject = some rid →
      ∃ r, st.getReply? rid = some r ∧ r.caller = some tid) ∧
  (∀ (rid : SeLe4n.ReplyId) (r : Reply) (tid : SeLe4n.ThreadId),
      st.getReply? rid = some r →
      r.caller = some tid →
      ∃ tcb, st.getTcb? tid = some tcb ∧ tcb.replyObject = some rid ∧
        ∃ (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
          tcb.ipcState = .blockedOnReply ep rt)

/-- SM6.D: per-core form of `blockedOnReplyHasReplyObject` (#7.4). -/
def blockedOnReplyHasReplyObject_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
      (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
      st.getTcb? tid = some tcb → threadHomeCore tcb = c →
      tcb.ipcState = .blockedOnReply ep rt →
      ∃ rid, tcb.replyObject = some rid

/-- SM6.D: per-core form of `replyCallerLinkage` (16th conjunct). -/
def replyCallerLinkage_perCore (st : SystemState) (c : CoreId) : Prop :=
  replyCallerLinkageReciprocal_perCore st c ∧ blockedOnReplyHasReplyObject_perCore st c

/-- SM6.D: per-core form of `pendingReceiveReplyWellFormed` (17th
conjunct).  Both the stash well-formedness clause and the injectivity
clause restrict on the (first) stashing receiver. -/
def pendingReceiveReplyWellFormed_perCore (st : SystemState) (c : CoreId) : Prop :=
  (∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (rid : SeLe4n.ReplyId),
    st.getTcb? tid = some tcb → threadHomeCore tcb = c →
    tcb.pendingReceiveReply = some rid →
    (∃ ep, tcb.ipcState = .blockedOnReceive ep) ∧
    (∃ r, st.getReply? rid = some r ∧ r.caller = none)) ∧
  (∀ (tid₁ tid₂ : SeLe4n.ThreadId) (tcb₁ tcb₂ : TCB) (rid : SeLe4n.ReplyId),
    st.getTcb? tid₁ = some tcb₁ → threadHomeCore tcb₁ = c →
    st.getTcb? tid₂ = some tcb₂ →
    tcb₁.pendingReceiveReply = some rid → tcb₂.pendingReceiveReply = some rid →
    tid₁ = tid₂)

/-- SM6.D: per-core form of `donationOwnerUnique` (Z7-H').  Restricted on
the first donation holder of the uniqueness pair. -/
def donationOwnerUnique_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid1 tid2 : SeLe4n.ThreadId) (tcb1 tcb2 : TCB)
    (scId1 scId2 : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId),
    st.getTcb? tid1 = some tcb1 → threadHomeCore tcb1 = c →
    st.getTcb? tid2 = some tcb2 →
    tcb1.schedContextBinding = .donated scId1 owner →
    tcb2.schedContextBinding = .donated scId2 owner →
    tid1 = tid2

/-- SM6.D: per-core form of `endpointQueueTailBlockedConsistent` (D4 /
F-2).  Restricted on the *tail thread* (mirroring the head form
`queueHeadBlockedConsistent_perCore`). -/
def endpointQueueTailBlockedConsistent_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (epId : SeLe4n.ObjId) (ep : Endpoint) (tl : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[epId]? = some (.endpoint ep) →
    st.getTcb? tl = some tcb → threadHomeCore tcb = c →
    (ep.receiveQ.tail = some tl → tcb.ipcState = .blockedOnReceive epId) ∧
    (ep.sendQ.tail = some tl →
      tcb.ipcState = .blockedOnSend epId ∨ tcb.ipcState = .blockedOnCall epId)

/-- SM6.D: per-core form of `queueNextTargetBlocked` (D4 Slice 2c).
Restricted on the link source `a` (matching
`queueNextBlockingConsistent_perCore`). -/
def queueNextTargetBlocked_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (a b : SeLe4n.ThreadId) (tcbA tcbB : TCB),
    st.getTcb? a = some tcbA → threadHomeCore tcbA = c →
    st.getTcb? b = some tcbB →
    tcbA.queueNext = some b →
    (∀ ep, tcbA.ipcState = .blockedOnReceive ep → tcbB.ipcState = .blockedOnReceive ep) ∧
    (∀ ep, (tcbA.ipcState = .blockedOnSend ep ∨ tcbA.ipcState = .blockedOnCall ep) →
      (tcbB.ipcState = .blockedOnSend ep ∨ tcbB.ipcState = .blockedOnCall ep))

-- ============================================================================
-- §2  Restriction bridges: the global conjunct weakens to every core's slice
-- ============================================================================

theorem ipcStateQueueMembershipConsistent_perCore_of_global {st : SystemState}
    (h : ipcStateQueueMembershipConsistent st) (c : CoreId) :
    ipcStateQueueMembershipConsistent_perCore st c := by
  intro tid tcb hTcb _
  have hG := h tid tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTcb)
  cases hIpc : tcb.ipcState with
  | blockedOnSend epId =>
      simp only [hIpc] at hG
      obtain ⟨ep, hEp, hReach⟩ := hG
      refine ⟨ep, hEp, ?_⟩
      rcases hReach with hHead | ⟨prev, prevTcb, hPrev, hNext⟩
      · exact Or.inl hHead
      · exact Or.inr ⟨prev, prevTcb, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hPrev, hNext⟩
  | blockedOnReceive epId =>
      simp only [hIpc] at hG
      obtain ⟨ep, hEp, hReach⟩ := hG
      refine ⟨ep, hEp, ?_⟩
      rcases hReach with hHead | ⟨prev, prevTcb, hPrev, hNext⟩
      · exact Or.inl hHead
      · exact Or.inr ⟨prev, prevTcb, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hPrev, hNext⟩
  | blockedOnCall epId =>
      simp only [hIpc] at hG
      obtain ⟨ep, hEp, hReach⟩ := hG
      refine ⟨ep, hEp, ?_⟩
      rcases hReach with hHead | ⟨prev, prevTcb, hPrev, hNext⟩
      · exact Or.inl hHead
      · exact Or.inr ⟨prev, prevTcb, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hPrev, hNext⟩
  | ready => trivial
  | blockedOnNotification nid => trivial
  | blockedOnReply ep rt => trivial

theorem endpointQueueNoDup_perCore_of_global {st : SystemState}
    (h : endpointQueueNoDup st) (c : CoreId) :
    endpointQueueNoDup_perCore st c := by
  intro oid ep hEp
  obtain ⟨hSelf, hDisj⟩ := h oid ep hEp
  exact ⟨fun tid tcb hTcb _ => hSelf tid tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTcb), hDisj⟩

theorem queueNextBlockingConsistent_perCore_of_global {st : SystemState}
    (h : queueNextBlockingConsistent st) (c : CoreId) :
    queueNextBlockingConsistent_perCore st c :=
  fun a b tcbA tcbB hA _ hB hNext =>
    h a b tcbA tcbB ((SystemState.getTcb?_eq_some_iff _ _ _).mp hA) ((SystemState.getTcb?_eq_some_iff _ _ _).mp hB) hNext

theorem queueHeadBlockedConsistent_perCore_of_global {st : SystemState}
    (h : queueHeadBlockedConsistent st) (c : CoreId) :
    queueHeadBlockedConsistent_perCore st c :=
  fun epId ep hd tcb hEp hTcb _ =>
    h epId ep hd tcb hEp ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTcb)

theorem tcbQueueLinkIntegrity_perCore_of_global {st : SystemState}
    (h : tcbQueueLinkIntegrity st) (c : CoreId) :
    tcbQueueLinkIntegrity_perCore st c := by
  refine ⟨fun a tcbA hA _ b hNext => ?_, fun b tcbB hB _ a hPrev => ?_⟩
  · obtain ⟨tcbB, hB, hBack⟩ := h.1 a tcbA ((SystemState.getTcb?_eq_some_iff _ _ _).mp hA) b hNext
    exact ⟨tcbB, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hB, hBack⟩
  · obtain ⟨tcbA, hA, hFwd⟩ := h.2 b tcbB ((SystemState.getTcb?_eq_some_iff _ _ _).mp hB) a hPrev
    exact ⟨tcbA, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hA, hFwd⟩

theorem tcbQueueChainAcyclic_perCore_of_global {st : SystemState}
    (h : tcbQueueChainAcyclic st) (c : CoreId) :
    tcbQueueChainAcyclic_perCore st c :=
  fun tid _ _ _ => h tid

theorem dualQueueSystemInvariant_perCore_of_global {st : SystemState}
    (h : dualQueueSystemInvariant st) (c : CoreId) :
    dualQueueSystemInvariant_perCore st c :=
  ⟨h.1, tcbQueueLinkIntegrity_perCore_of_global h.2.1 c,
   tcbQueueChainAcyclic_perCore_of_global h.2.2 c⟩

theorem allPendingMessagesBounded_perCore_of_global {st : SystemState}
    (h : allPendingMessagesBounded st) (c : CoreId) :
    allPendingMessagesBounded_perCore st c :=
  fun tid tcb msg hTcb _ hMsg => h tid tcb msg ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTcb) hMsg

theorem waitingThreadsPendingMessageNone_perCore_of_global {st : SystemState}
    (h : waitingThreadsPendingMessageNone st) (c : CoreId) :
    waitingThreadsPendingMessageNone_perCore st c :=
  fun tid tcb hTcb _ => h tid tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTcb)

theorem blockedThreadTimeoutConsistent_perCore_of_global {st : SystemState}
    (h : blockedThreadTimeoutConsistent st) (c : CoreId) :
    blockedThreadTimeoutConsistent_perCore st c := by
  intro tid tcb scId hTcb _ hBudget
  obtain ⟨⟨sc, hSc⟩, hBlk⟩ := h tid tcb scId ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTcb) hBudget
  exact ⟨⟨sc, (SystemState.getSchedContext?_eq_some_iff st scId sc).mpr hSc⟩, hBlk⟩

theorem donationChainAcyclic_perCore_of_global {st : SystemState}
    (h : donationChainAcyclic st) (c : CoreId) :
    donationChainAcyclic_perCore st c :=
  fun tid1 tid2 tcb1 tcb2 scId1 scId2 h1 _ h2 hB1 hB2 =>
    h tid1 tid2 tcb1 tcb2 scId1 scId2 ((SystemState.getTcb?_eq_some_iff _ _ _).mp h1) ((SystemState.getTcb?_eq_some_iff _ _ _).mp h2) hB1 hB2

theorem donationOwnerValid_perCore_of_global {st : SystemState}
    (h : donationOwnerValid st) (c : CoreId) :
    donationOwnerValid_perCore st c := by
  intro tid tcb scId owner hTcb _ hBind
  obtain ⟨⟨sc, hSc, hBound⟩, ⟨ownerTcb, hOwner, hUnbound, hReply⟩⟩ :=
    h tid tcb scId owner ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTcb) hBind
  exact ⟨⟨sc, (SystemState.getSchedContext?_eq_some_iff st scId sc).mpr hSc, hBound⟩,
    ⟨ownerTcb, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hOwner, hUnbound, hReply⟩⟩

theorem donationBudgetTransfer_perCore_of_global {st : SystemState}
    (h : donationBudgetTransfer st) (c : CoreId) :
    donationBudgetTransfer_perCore st c :=
  fun tid1 tid2 tcb1 tcb2 scId h1 _ h2 hNe hS1 hS2 =>
    h tid1 tid2 tcb1 tcb2 scId ((SystemState.getTcb?_eq_some_iff _ _ _).mp h1) ((SystemState.getTcb?_eq_some_iff _ _ _).mp h2) hNe hS1 hS2

theorem blockedOnReplyHasTarget_perCore_of_global {st : SystemState}
    (h : blockedOnReplyHasTarget st) (c : CoreId) :
    blockedOnReplyHasTarget_perCore st c :=
  fun tid tcb endpointId replyTarget hTcb _ hIpc =>
    h tid tcb endpointId replyTarget ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTcb) hIpc

theorem replyCallerLinkageReciprocal_perCore_of_global {st : SystemState}
    (h : replyCallerLinkageReciprocal st) (c : CoreId) :
    replyCallerLinkageReciprocal_perCore st c := by
  refine ⟨fun tid tcb rid hTcb _ hRep => ?_, fun rid r tid hRep hCaller => ?_⟩
  · obtain ⟨r, hR, hBack⟩ := h.1 tid tcb rid ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTcb) hRep
    exact ⟨r, (SystemState.getReply?_eq_some_iff st rid r).mpr hR, hBack⟩
  · obtain ⟨tcb, hTcb, hFwd, hBlk⟩ :=
      h.2 rid r tid ((SystemState.getReply?_eq_some_iff st rid r).mp hRep) hCaller
    exact ⟨tcb, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hTcb, hFwd, hBlk⟩

theorem blockedOnReplyHasReplyObject_perCore_of_global {st : SystemState}
    (h : blockedOnReplyHasReplyObject st) (c : CoreId) :
    blockedOnReplyHasReplyObject_perCore st c :=
  fun tid tcb ep rt hTcb _ hIpc => h tid tcb ep rt ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTcb) hIpc

theorem replyCallerLinkage_perCore_of_global {st : SystemState}
    (h : replyCallerLinkage st) (c : CoreId) :
    replyCallerLinkage_perCore st c :=
  ⟨replyCallerLinkageReciprocal_perCore_of_global h.1 c,
   blockedOnReplyHasReplyObject_perCore_of_global h.2 c⟩

theorem pendingReceiveReplyWellFormed_perCore_of_global {st : SystemState}
    (h : pendingReceiveReplyWellFormed st) (c : CoreId) :
    pendingReceiveReplyWellFormed_perCore st c :=
  ⟨fun tid tcb rid hTcb _ hStash => h.1 tid tcb rid hTcb hStash,
   fun tid₁ tid₂ tcb₁ tcb₂ rid h1 _ h2 hS1 hS2 => h.2 tid₁ tid₂ tcb₁ tcb₂ rid h1 h2 hS1 hS2⟩

theorem donationOwnerUnique_perCore_of_global {st : SystemState}
    (h : donationOwnerUnique st) (c : CoreId) :
    donationOwnerUnique_perCore st c :=
  fun tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 _ h2 hB1 hB2 =>
    h tid1 tid2 tcb1 tcb2 scId1 scId2 owner ((SystemState.getTcb?_eq_some_iff _ _ _).mp h1) ((SystemState.getTcb?_eq_some_iff _ _ _).mp h2) hB1 hB2

theorem endpointQueueTailBlockedConsistent_perCore_of_global {st : SystemState}
    (h : endpointQueueTailBlockedConsistent st) (c : CoreId) :
    endpointQueueTailBlockedConsistent_perCore st c :=
  fun epId ep tl tcb hEp hTcb _ =>
    h epId ep tl tcb hEp ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTcb)

theorem queueNextTargetBlocked_perCore_of_global {st : SystemState}
    (h : queueNextTargetBlocked st) (c : CoreId) :
    queueNextTargetBlocked_perCore st c :=
  fun a b tcbA tcbB hA _ hB hNext =>
    h a b tcbA tcbB ((SystemState.getTcb?_eq_some_iff _ _ _).mp hA) ((SystemState.getTcb?_eq_some_iff _ _ _).mp hB) hNext

-- ============================================================================
-- §3  Recovery bridges: the ∀-core slices jointly recover the global conjunct
-- ============================================================================
--
-- Each proof instantiates the per-core family at the subject thread's own
-- home core (`threadHomeCore tcb`), so no assumption about the core
-- topology is needed — the slices form an exact cover of the thread
-- domain.

theorem ipcStateQueueMembershipConsistent_of_forall_perCore {st : SystemState}
    (h : ∀ c, ipcStateQueueMembershipConsistent_perCore st c) :
    ipcStateQueueMembershipConsistent st := by
  intro tid tcb hRaw
  have hPC := h (threadHomeCore tcb) tid tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hRaw) rfl
  cases hIpc : tcb.ipcState with
  | blockedOnSend epId =>
      simp only [hIpc] at hPC
      obtain ⟨ep, hEp, hReach⟩ := hPC
      refine ⟨ep, hEp, ?_⟩
      rcases hReach with hHead | ⟨prev, prevTcb, hPrev, hNext⟩
      · exact Or.inl hHead
      · exact Or.inr ⟨prev, prevTcb, (SystemState.getTcb?_eq_some_iff _ _ _).mp hPrev, hNext⟩
  | blockedOnReceive epId =>
      simp only [hIpc] at hPC
      obtain ⟨ep, hEp, hReach⟩ := hPC
      refine ⟨ep, hEp, ?_⟩
      rcases hReach with hHead | ⟨prev, prevTcb, hPrev, hNext⟩
      · exact Or.inl hHead
      · exact Or.inr ⟨prev, prevTcb, (SystemState.getTcb?_eq_some_iff _ _ _).mp hPrev, hNext⟩
  | blockedOnCall epId =>
      simp only [hIpc] at hPC
      obtain ⟨ep, hEp, hReach⟩ := hPC
      refine ⟨ep, hEp, ?_⟩
      rcases hReach with hHead | ⟨prev, prevTcb, hPrev, hNext⟩
      · exact Or.inl hHead
      · exact Or.inr ⟨prev, prevTcb, (SystemState.getTcb?_eq_some_iff _ _ _).mp hPrev, hNext⟩
  | ready => trivial
  | blockedOnNotification nid => trivial
  | blockedOnReply ep rt => trivial

theorem endpointQueueNoDup_of_forall_perCore {st : SystemState}
    (h : ∀ c, endpointQueueNoDup_perCore st c) :
    endpointQueueNoDup st := by
  intro oid ep hEp
  refine ⟨fun tid tcb hRaw => ?_, (h bootCoreId oid ep hEp).2⟩
  exact (h (threadHomeCore tcb) oid ep hEp).1 tid tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hRaw) rfl

theorem queueNextBlockingConsistent_of_forall_perCore {st : SystemState}
    (h : ∀ c, queueNextBlockingConsistent_perCore st c) :
    queueNextBlockingConsistent st :=
  fun a b tcbA tcbB hA hB hNext =>
    h (threadHomeCore tcbA) a b tcbA tcbB ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hA) rfl ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hB) hNext

theorem queueHeadBlockedConsistent_of_forall_perCore {st : SystemState}
    (h : ∀ c, queueHeadBlockedConsistent_perCore st c) :
    queueHeadBlockedConsistent st :=
  fun epId ep hd tcb hEp hTcb =>
    h (threadHomeCore tcb) epId ep hd tcb hEp ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hTcb) rfl

theorem tcbQueueLinkIntegrity_of_forall_perCore {st : SystemState}
    (h : ∀ c, tcbQueueLinkIntegrity_perCore st c) :
    tcbQueueLinkIntegrity st := by
  refine ⟨fun a tcbA hA b hNext => ?_, fun b tcbB hB a hPrev => ?_⟩
  · obtain ⟨tcbB, hB, hBack⟩ :=
      (h (threadHomeCore tcbA)).1 a tcbA ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hA) rfl b hNext
    exact ⟨tcbB, (SystemState.getTcb?_eq_some_iff _ _ _).mp hB, hBack⟩
  · obtain ⟨tcbA, hA, hFwd⟩ :=
      (h (threadHomeCore tcbB)).2 b tcbB ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hB) rfl a hPrev
    exact ⟨tcbA, (SystemState.getTcb?_eq_some_iff _ _ _).mp hA, hFwd⟩

theorem tcbQueueChainAcyclic_of_forall_perCore {st : SystemState}
    (h : ∀ c, tcbQueueChainAcyclic_perCore st c) :
    tcbQueueChainAcyclic st := by
  intro tid hPath
  obtain ⟨mid, tcb, hObj, _⟩ := hPath.firstEdge
  exact h (threadHomeCore tcb) tid tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hObj) rfl hPath

theorem dualQueueSystemInvariant_of_forall_perCore {st : SystemState}
    (h : ∀ c, dualQueueSystemInvariant_perCore st c) :
    dualQueueSystemInvariant st :=
  ⟨(h bootCoreId).1,
   tcbQueueLinkIntegrity_of_forall_perCore (fun c => (h c).2.1),
   tcbQueueChainAcyclic_of_forall_perCore (fun c => (h c).2.2)⟩

theorem allPendingMessagesBounded_of_forall_perCore {st : SystemState}
    (h : ∀ c, allPendingMessagesBounded_perCore st c) :
    allPendingMessagesBounded st :=
  fun tid tcb msg hRaw hMsg =>
    h (threadHomeCore tcb) tid tcb msg ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hRaw) rfl hMsg

theorem waitingThreadsPendingMessageNone_of_forall_perCore {st : SystemState}
    (h : ∀ c, waitingThreadsPendingMessageNone_perCore st c) :
    waitingThreadsPendingMessageNone st :=
  fun tid tcb hRaw =>
    h (threadHomeCore tcb) tid tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hRaw) rfl

theorem blockedThreadTimeoutConsistent_of_forall_perCore {st : SystemState}
    (h : ∀ c, blockedThreadTimeoutConsistent_perCore st c) :
    blockedThreadTimeoutConsistent st := by
  intro tid tcb scId hRaw hBudget
  obtain ⟨⟨sc, hSc⟩, hBlk⟩ :=
    h (threadHomeCore tcb) tid tcb scId ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hRaw) rfl hBudget
  exact ⟨⟨sc, (SystemState.getSchedContext?_eq_some_iff st scId sc).mp hSc⟩, hBlk⟩

theorem donationChainAcyclic_of_forall_perCore {st : SystemState}
    (h : ∀ c, donationChainAcyclic_perCore st c) :
    donationChainAcyclic st :=
  fun tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2 =>
    h (threadHomeCore tcb1) tid1 tid2 tcb1 tcb2 scId1 scId2
      ((SystemState.getTcb?_eq_some_iff _ _ _).mpr h1) rfl ((SystemState.getTcb?_eq_some_iff _ _ _).mpr h2) hB1 hB2

theorem donationOwnerValid_of_forall_perCore {st : SystemState}
    (h : ∀ c, donationOwnerValid_perCore st c) :
    donationOwnerValid st := by
  intro tid tcb scId owner hRaw hBind
  obtain ⟨⟨sc, hSc, hBound⟩, ⟨ownerTcb, hOwner, hUnbound, hReply⟩⟩ :=
    h (threadHomeCore tcb) tid tcb scId owner ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hRaw) rfl hBind
  exact ⟨⟨sc, (SystemState.getSchedContext?_eq_some_iff st scId sc).mp hSc, hBound⟩,
    ⟨ownerTcb, (SystemState.getTcb?_eq_some_iff _ _ _).mp hOwner, hUnbound, hReply⟩⟩

theorem donationBudgetTransfer_of_forall_perCore {st : SystemState}
    (h : ∀ c, donationBudgetTransfer_perCore st c) :
    donationBudgetTransfer st :=
  fun tid1 tid2 tcb1 tcb2 scId h1 h2 hNe hS1 hS2 =>
    h (threadHomeCore tcb1) tid1 tid2 tcb1 tcb2 scId
      ((SystemState.getTcb?_eq_some_iff _ _ _).mpr h1) rfl ((SystemState.getTcb?_eq_some_iff _ _ _).mpr h2) hNe hS1 hS2

theorem blockedOnReplyHasTarget_of_forall_perCore {st : SystemState}
    (h : ∀ c, blockedOnReplyHasTarget_perCore st c) :
    blockedOnReplyHasTarget st :=
  fun tid tcb endpointId replyTarget hRaw hIpc =>
    h (threadHomeCore tcb) tid tcb endpointId replyTarget ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hRaw) rfl hIpc

theorem replyCallerLinkageReciprocal_of_forall_perCore {st : SystemState}
    (h : ∀ c, replyCallerLinkageReciprocal_perCore st c) :
    replyCallerLinkageReciprocal st := by
  refine ⟨fun tid tcb rid hRaw hRep => ?_, fun rid r tid hRep hCaller => ?_⟩
  · obtain ⟨r, hR, hBack⟩ :=
      (h (threadHomeCore tcb)).1 tid tcb rid ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hRaw) rfl hRep
    exact ⟨r, (SystemState.getReply?_eq_some_iff st rid r).mp hR, hBack⟩
  · obtain ⟨tcb, hTcb, hFwd, hBlk⟩ :=
      (h bootCoreId).2 rid r tid ((SystemState.getReply?_eq_some_iff st rid r).mpr hRep) hCaller
    exact ⟨tcb, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTcb, hFwd, hBlk⟩

theorem blockedOnReplyHasReplyObject_of_forall_perCore {st : SystemState}
    (h : ∀ c, blockedOnReplyHasReplyObject_perCore st c) :
    blockedOnReplyHasReplyObject st :=
  fun tid tcb ep rt hRaw hIpc =>
    h (threadHomeCore tcb) tid tcb ep rt ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hRaw) rfl hIpc

theorem replyCallerLinkage_of_forall_perCore {st : SystemState}
    (h : ∀ c, replyCallerLinkage_perCore st c) :
    replyCallerLinkage st :=
  ⟨replyCallerLinkageReciprocal_of_forall_perCore (fun c => (h c).1),
   blockedOnReplyHasReplyObject_of_forall_perCore (fun c => (h c).2)⟩

theorem pendingReceiveReplyWellFormed_of_forall_perCore {st : SystemState}
    (h : ∀ c, pendingReceiveReplyWellFormed_perCore st c) :
    pendingReceiveReplyWellFormed st :=
  ⟨fun tid tcb rid hTcb hStash =>
      (h (threadHomeCore tcb)).1 tid tcb rid hTcb rfl hStash,
   fun tid₁ tid₂ tcb₁ tcb₂ rid h1 h2 hS1 hS2 =>
      (h (threadHomeCore tcb₁)).2 tid₁ tid₂ tcb₁ tcb₂ rid h1 rfl h2 hS1 hS2⟩

theorem donationOwnerUnique_of_forall_perCore {st : SystemState}
    (h : ∀ c, donationOwnerUnique_perCore st c) :
    donationOwnerUnique st :=
  fun tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2 =>
    h (threadHomeCore tcb1) tid1 tid2 tcb1 tcb2 scId1 scId2 owner
      ((SystemState.getTcb?_eq_some_iff _ _ _).mpr h1) rfl ((SystemState.getTcb?_eq_some_iff _ _ _).mpr h2) hB1 hB2

theorem endpointQueueTailBlockedConsistent_of_forall_perCore {st : SystemState}
    (h : ∀ c, endpointQueueTailBlockedConsistent_perCore st c) :
    endpointQueueTailBlockedConsistent st :=
  fun epId ep tl tcb hEp hTcb =>
    h (threadHomeCore tcb) epId ep tl tcb hEp ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hTcb) rfl

theorem queueNextTargetBlocked_of_forall_perCore {st : SystemState}
    (h : ∀ c, queueNextTargetBlocked_perCore st c) :
    queueNextTargetBlocked st :=
  fun a b tcbA tcbB hA hB hNext =>
    h (threadHomeCore tcbA) a b tcbA tcbB ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hA) rfl ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hB) hNext

-- ============================================================================
-- §4  Exactness: per-conjunct ∀-core ↔ global equivalences (SM6.D.3–D.6)
-- ============================================================================

/-- SM6.D.3 exactness: the ∀-core family of per-core queue-membership
slices is *equivalent* to the global conjunct — the restriction loses
nothing. -/
theorem ipcStateQueueMembershipConsistent_smp_iff (st : SystemState) :
    (∀ c, ipcStateQueueMembershipConsistent_perCore st c) ↔
      ipcStateQueueMembershipConsistent st :=
  ⟨ipcStateQueueMembershipConsistent_of_forall_perCore,
   fun h c => ipcStateQueueMembershipConsistent_perCore_of_global h c⟩

/-- SM6.D.4 exactness. -/
theorem endpointQueueNoDup_smp_iff (st : SystemState) :
    (∀ c, endpointQueueNoDup_perCore st c) ↔ endpointQueueNoDup st :=
  ⟨endpointQueueNoDup_of_forall_perCore,
   fun h c => endpointQueueNoDup_perCore_of_global h c⟩

/-- SM6.D.5 exactness. -/
theorem queueNextBlockingConsistent_smp_iff (st : SystemState) :
    (∀ c, queueNextBlockingConsistent_perCore st c) ↔ queueNextBlockingConsistent st :=
  ⟨queueNextBlockingConsistent_of_forall_perCore,
   fun h c => queueNextBlockingConsistent_perCore_of_global h c⟩

/-- SM6.D.6 exactness. -/
theorem queueHeadBlockedConsistent_smp_iff (st : SystemState) :
    (∀ c, queueHeadBlockedConsistent_perCore st c) ↔ queueHeadBlockedConsistent st :=
  ⟨queueHeadBlockedConsistent_of_forall_perCore,
   fun h c => queueHeadBlockedConsistent_perCore_of_global h c⟩

-- ============================================================================
-- §5  SM6.D.1: the per-core IPC invariant bundle aggregate
-- ============================================================================

/-- WS-SM SM6.D.1: **the per-core IPC invariant bundle** — core `c`'s view
of `ipcInvariantFull`, one field per conjunct in the same order.

The plan (`SMP_CROSS_CORE_IPC_PLAN.md` §3.3) sketched this aggregate over
the fifteen R4-era conjuncts; the bundle grew to twenty during the SM6.D
reply-object hardening (reply↔caller linkage, server-first receive stash,
donation-owner uniqueness, queue-tail blocking, strict link-target
blocking), and this per-core form mirrors the **current** twenty-conjunct
`ipcInvariantFull` — dropping the five newer conjuncts from the per-core
view would re-open on the SMP surface exactly the false-assurance gaps
they closed (a stale reply cap acting on the wrong caller, a stranded
receive stash, a double-spent donation).

Thread-subject conjuncts are restricted to the threads homed on `c`;
shared-object clauses (`ipcInvariant`, `badgeWellFormed`, the embedded
endpoint well-formedness / head-disjointness / backward reply-linkage
clauses) are carried whole in every core's view; the scheduler-reading
`passiveServerIdle` uses the SM4.D per-core form (core `c`'s scheduler
slots).  Declared as a `structure` so consumers use named projections
(`h.queueHeadBlockedConsistent`) rather than fragile `.2.2.…` chains —
the AN3-B lesson applied from day one. -/
structure ipcInvariantFull_perCore (st : SystemState) (c : CoreId) : Prop where
  ipcInvariant : ipcInvariant st
  dualQueueSystemInvariant : dualQueueSystemInvariant_perCore st c
  allPendingMessagesBounded : allPendingMessagesBounded_perCore st c
  badgeWellFormed : badgeWellFormed st
  waitingThreadsPendingMessageNone : waitingThreadsPendingMessageNone_perCore st c
  endpointQueueNoDup : endpointQueueNoDup_perCore st c
  ipcStateQueueMembershipConsistent : ipcStateQueueMembershipConsistent_perCore st c
  queueNextBlockingConsistent : queueNextBlockingConsistent_perCore st c
  queueHeadBlockedConsistent : queueHeadBlockedConsistent_perCore st c
  blockedThreadTimeoutConsistent : blockedThreadTimeoutConsistent_perCore st c
  donationChainAcyclic : donationChainAcyclic_perCore st c
  donationOwnerValid : donationOwnerValid_perCore st c
  passiveServerIdle : passiveServerIdle_perCore st c
  donationBudgetTransfer : donationBudgetTransfer_perCore st c
  blockedOnReplyHasTarget : blockedOnReplyHasTarget_perCore st c
  replyCallerLinkage : replyCallerLinkage_perCore st c
  pendingReceiveReplyWellFormed : pendingReceiveReplyWellFormed_perCore st c
  donationOwnerUnique : donationOwnerUnique_perCore st c
  endpointQueueTailBlockedConsistent : endpointQueueTailBlockedConsistent_perCore st c
  queueNextTargetBlocked : queueNextTargetBlocked_perCore st c

/-- WS-SM SM6.D.1: the ∀-core SMP aggregate — every core's view of the
IPC invariant bundle holds. -/
def ipcInvariantFull_smp (st : SystemState) : Prop :=
  ∀ c : CoreId, ipcInvariantFull_perCore st c

theorem ipcInvariantFull_smp_at {st : SystemState} (c : CoreId)
    (h : ipcInvariantFull_smp st) : ipcInvariantFull_perCore st c := h c

/-- SM6.D.1 restriction: the global bundle weakens to core `c`'s view,
given core `c`'s slice of the one scheduler-reading conjunct
(`passiveServerIdle_perCore` — the global bundle carries only the
boot-core instance). -/
theorem ipcInvariantFull_perCore_of_full {st : SystemState} {c : CoreId}
    (h : ipcInvariantFull st) (hPsi : passiveServerIdle_perCore st c) :
    ipcInvariantFull_perCore st c where
  ipcInvariant := h.ipcInvariant
  dualQueueSystemInvariant := dualQueueSystemInvariant_perCore_of_global h.dualQueueSystemInvariant c
  allPendingMessagesBounded := allPendingMessagesBounded_perCore_of_global h.allPendingMessagesBounded c
  badgeWellFormed := h.badgeWellFormed
  waitingThreadsPendingMessageNone :=
    waitingThreadsPendingMessageNone_perCore_of_global h.waitingThreadsPendingMessageNone c
  endpointQueueNoDup := endpointQueueNoDup_perCore_of_global h.endpointQueueNoDup c
  ipcStateQueueMembershipConsistent :=
    ipcStateQueueMembershipConsistent_perCore_of_global h.ipcStateQueueMembershipConsistent c
  queueNextBlockingConsistent :=
    queueNextBlockingConsistent_perCore_of_global h.queueNextBlockingConsistent c
  queueHeadBlockedConsistent :=
    queueHeadBlockedConsistent_perCore_of_global h.queueHeadBlockedConsistent c
  blockedThreadTimeoutConsistent :=
    blockedThreadTimeoutConsistent_perCore_of_global h.blockedThreadTimeoutConsistent c
  donationChainAcyclic := donationChainAcyclic_perCore_of_global h.donationChainAcyclic c
  donationOwnerValid := donationOwnerValid_perCore_of_global h.donationOwnerValid c
  passiveServerIdle := hPsi
  donationBudgetTransfer := donationBudgetTransfer_perCore_of_global h.donationBudgetTransfer c
  blockedOnReplyHasTarget := blockedOnReplyHasTarget_perCore_of_global h.blockedOnReplyHasTarget c
  replyCallerLinkage := replyCallerLinkage_perCore_of_global h.replyCallerLinkage c
  pendingReceiveReplyWellFormed :=
    pendingReceiveReplyWellFormed_perCore_of_global h.pendingReceiveReplyWellFormed c
  donationOwnerUnique := donationOwnerUnique_perCore_of_global h.donationOwnerUnique c
  endpointQueueTailBlockedConsistent :=
    endpointQueueTailBlockedConsistent_perCore_of_global h.endpointQueueTailBlockedConsistent c
  queueNextTargetBlocked := queueNextTargetBlocked_perCore_of_global h.queueNextTargetBlocked c

/-- SM6.D.1 recovery: the ∀-core SMP aggregate recovers the full global
bundle (each restricted conjunct instantiated at its subject's home core;
`passiveServerIdle` at the boot core via the SM4.D bridge). -/
theorem ipcInvariantFull_of_smp {st : SystemState}
    (h : ipcInvariantFull_smp st) : ipcInvariantFull st :=
  ⟨(h bootCoreId).ipcInvariant,
   dualQueueSystemInvariant_of_forall_perCore (fun c => (h c).dualQueueSystemInvariant),
   allPendingMessagesBounded_of_forall_perCore (fun c => (h c).allPendingMessagesBounded),
   (h bootCoreId).badgeWellFormed,
   waitingThreadsPendingMessageNone_of_forall_perCore
     (fun c => (h c).waitingThreadsPendingMessageNone),
   endpointQueueNoDup_of_forall_perCore (fun c => (h c).endpointQueueNoDup),
   ipcStateQueueMembershipConsistent_of_forall_perCore
     (fun c => (h c).ipcStateQueueMembershipConsistent),
   queueNextBlockingConsistent_of_forall_perCore (fun c => (h c).queueNextBlockingConsistent),
   queueHeadBlockedConsistent_of_forall_perCore (fun c => (h c).queueHeadBlockedConsistent),
   blockedThreadTimeoutConsistent_of_forall_perCore
     (fun c => (h c).blockedThreadTimeoutConsistent),
   donationChainAcyclic_of_forall_perCore (fun c => (h c).donationChainAcyclic),
   donationOwnerValid_of_forall_perCore (fun c => (h c).donationOwnerValid),
   (passiveServerIdle_perCore_bootCore_iff st).mp (h bootCoreId).passiveServerIdle,
   donationBudgetTransfer_of_forall_perCore (fun c => (h c).donationBudgetTransfer),
   blockedOnReplyHasTarget_of_forall_perCore (fun c => (h c).blockedOnReplyHasTarget),
   replyCallerLinkage_of_forall_perCore (fun c => (h c).replyCallerLinkage),
   pendingReceiveReplyWellFormed_of_forall_perCore
     (fun c => (h c).pendingReceiveReplyWellFormed),
   donationOwnerUnique_of_forall_perCore (fun c => (h c).donationOwnerUnique),
   endpointQueueTailBlockedConsistent_of_forall_perCore
     (fun c => (h c).endpointQueueTailBlockedConsistent),
   queueNextTargetBlocked_of_forall_perCore (fun c => (h c).queueNextTargetBlocked)⟩

/-- SM6.D.1 recovery to the plan's fifteen-conjunct structural core
(`ipcInvariantCore` — the "15 conjuncts post-R4" the plan names). -/
theorem ipcInvariantCore_of_smp {st : SystemState}
    (h : ipcInvariantFull_smp st) : ipcInvariantCore st :=
  (ipcInvariantFull_of_smp h).toCore

/-- SM6.D.1 **exact decomposition**: the ∀-core SMP bundle is equivalent
to the global bundle plus the ∀-core slices of the one scheduler-reading
conjunct.  This is the precise sense in which "the 15-conjunct bundle
carries through per-core structurally unchanged" (plan §3.3): nothing is
weakened, and the only genuinely new SMP content is the per-core
passive-idle discipline. -/
theorem ipcInvariantFull_smp_iff_full_and_passive_smp (st : SystemState) :
    ipcInvariantFull_smp st ↔ ipcInvariantFull st ∧ passiveServerIdle_smp st :=
  ⟨fun h => ⟨ipcInvariantFull_of_smp h, fun c => (h c).passiveServerIdle⟩,
   fun h c => ipcInvariantFull_perCore_of_full h.1 (h.2 c)⟩

-- ============================================================================
-- §6  Default-state witness: every core's bundle view holds at boot
-- ============================================================================

/-- Local helper (mirrors the SM4.D private helper): the default system
state's object store is empty. -/
private theorem default_objects_getElem_none' (oid : SeLe4n.ObjId) :
    (default : SystemState).objects[oid]? = none := by
  simp only [RHTable_getElem?_eq_get?]
  exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_empty 16 (by omega) oid

/-- Local helper: `getTcb?` is `none` for every thread on the default state. -/
private theorem default_getTcb?_none' (tid : SeLe4n.ThreadId) :
    (default : SystemState).getTcb? tid = none := by
  unfold SystemState.getTcb?
  rw [default_objects_getElem_none']

/-- Local helper: no TCB lookup succeeds on the default state. -/
private theorem default_no_tcb {tid : SeLe4n.ThreadId} {tcb : TCB}
    (h : (default : SystemState).getTcb? tid = some tcb) : False := by
  rw [default_getTcb?_none'] at h
  cases h

/-- WS-SM SM6.D: the freshly-booted (empty) system satisfies every core's
bundle view — the boot witness that the per-core bundle is establishable,
not merely preservable. -/
theorem default_ipcInvariantFull_perCore (c : CoreId) :
    ipcInvariantFull_perCore (default : SystemState) c where
  ipcInvariant := fun oid ntfn h => by
    rw [default_objects_getElem_none'] at h; cases h
  dualQueueSystemInvariant :=
    ⟨fun epId ep h => (by rw [default_objects_getElem_none'] at h; cases h),
     ⟨fun a tcbA hA _ b _ => absurd hA default_no_tcb,
      fun b tcbB hB _ a _ => absurd hB default_no_tcb⟩,
     fun tid tcb hTcb _ _ => default_no_tcb hTcb⟩
  allPendingMessagesBounded := fun tid tcb msg hTcb _ _ => absurd hTcb default_no_tcb
  badgeWellFormed :=
    ⟨fun oid ntfn badge h _ => (by rw [default_objects_getElem_none'] at h; cases h),
     fun oid cn slot cap badge h _ _ => (by rw [default_objects_getElem_none'] at h; cases h)⟩
  waitingThreadsPendingMessageNone := fun tid tcb hTcb _ => absurd hTcb default_no_tcb
  endpointQueueNoDup := fun oid ep h => by rw [default_objects_getElem_none'] at h; cases h
  ipcStateQueueMembershipConsistent := fun tid tcb hTcb _ => absurd hTcb default_no_tcb
  queueNextBlockingConsistent := fun a b tcbA tcbB hA _ _ _ => absurd hA default_no_tcb
  queueHeadBlockedConsistent := fun epId ep hd tcb hEp _ _ => by
    rw [default_objects_getElem_none'] at hEp; cases hEp
  blockedThreadTimeoutConsistent := fun tid tcb scId hTcb _ _ => absurd hTcb default_no_tcb
  donationChainAcyclic := fun tid1 tid2 tcb1 tcb2 scId1 scId2 h1 _ _ _ _ =>
    default_no_tcb h1
  donationOwnerValid := fun tid tcb scId owner hTcb _ _ => absurd hTcb default_no_tcb
  passiveServerIdle := default_passiveServerIdle_perCore c
  donationBudgetTransfer := fun tid1 tid2 tcb1 tcb2 scId h1 _ _ _ _ _ =>
    default_no_tcb h1
  blockedOnReplyHasTarget := fun tid tcb endpointId replyTarget hTcb _ _ =>
    absurd hTcb default_no_tcb
  replyCallerLinkage :=
    ⟨⟨fun tid tcb rid hTcb _ _ => absurd hTcb default_no_tcb,
      fun rid r tid hRep _ => (by
        rw [SystemState.getReply?_eq_some_iff _ rid r, default_objects_getElem_none'] at hRep
        cases hRep)⟩,
     fun tid tcb ep rt hTcb _ _ => absurd hTcb default_no_tcb⟩
  pendingReceiveReplyWellFormed :=
    ⟨fun tid tcb rid hTcb _ _ => absurd hTcb default_no_tcb,
     fun tid₁ tid₂ tcb₁ tcb₂ rid h1 _ _ _ _ => absurd h1 default_no_tcb⟩
  donationOwnerUnique := fun tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 _ _ _ _ =>
    absurd h1 default_no_tcb
  endpointQueueTailBlockedConsistent := fun epId ep tl tcb hEp _ _ => by
    rw [default_objects_getElem_none'] at hEp; cases hEp
  queueNextTargetBlocked := fun a b tcbA tcbB hA _ _ _ => absurd hA default_no_tcb

/-- WS-SM SM6.D: the default state satisfies the ∀-core SMP aggregate. -/
theorem default_ipcInvariantFull_smp : ipcInvariantFull_smp (default : SystemState) :=
  fun c => default_ipcInvariantFull_perCore c

end SeLe4n.Kernel
