-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

namespace SeLe4n.Kernel.PriorityInheritance

open SeLe4n.Model

-- ============================================================================
-- D4-C1: blockedOnThread predicate
-- ============================================================================

/-- D4-C1: `waiter` is directly blocked on `server` via Reply IPC.
True when `waiter` has `ipcState = .blockedOnReply epId (some server)`.
Returns Bool for decidable runtime use. -/
def blockedOnThread (st : SystemState) (waiter server : ThreadId) : Bool :=
  match st.objects[waiter.toObjId]? with
  | some (.tcb tcb) =>
    match tcb.ipcState with
    | .blockedOnReply _ (some target) => target == server
    | _ => false
  | _ => false

/-- D4-C1: Propositional form of `blockedOnThread`. -/
def BlockedOnThread (st : SystemState) (waiter server : ThreadId) : Prop :=
  ∃ tcb : TCB, st.objects[waiter.toObjId]? = some (.tcb tcb) ∧
    ∃ epId : ObjId, tcb.ipcState = .blockedOnReply epId (some server)

-- ============================================================================
-- D4-C2: waitersOf (direct dependents)
-- ============================================================================

/-- D4-C2: Collect all threads directly blocked on `tid` via Reply IPC.
Folds over the object index, filtering for TCBs with `blockedOnReply _ (some tid)`. -/
def waitersOf (st : SystemState) (tid : ThreadId) : List ThreadId :=
  st.objectIndex.filterMap fun objId =>
    match st.objects[objId]? with
    | some (KernelObject.tcb tcb) =>
      match tcb.ipcState with
      | .blockedOnReply _ (some target) =>
        if target == tid then some tcb.tid else none
      | _ => none
    | _ => none

-- ============================================================================
-- D4-C3: blockingChain (transitive closure — upward walk)
-- ============================================================================

/-- D4-C3: Walk the blocking chain upward from `tid`.
If `tid` has `ipcState = .blockedOnReply _ (some server)`, prepend `server`
and recurse. Terminates when fuel exhausted or thread not in blockedOnReply.

**Fuel semantics**: The `fuel` parameter defaults to `st.objectIndex.length`
(the number of objects in the store). This is sufficient because:
- Each step of the chain visits a distinct thread (the `server` field).
- The `blockingAcyclic` invariant guarantees no cycles in the blocking graph,
  so the chain length is bounded by the number of threads, which is bounded
  by `objectIndex.length`. AF1-B integrates `blockingAcyclic` into
  `crossSubsystemInvariant` (CrossSubsystem.lean) as the 10th predicate.
  AI6-E (L-15): No separate depth constant (e.g., `maxBlockingDepth`) is
  defined — the `objectIndex.length` fuel default is the sole bound.

**Truncation behavior**: If fuel reaches 0, returns `[]` (silent truncation).
Under the `blockingAcyclic` invariant this never happens — fuel is always
sufficient. If the invariant is violated (cyclic blocking graph), PIP
propagation stops early at the cycle, and threads in the cycle retain stale
priority boosts until the cycle is broken by an IPC completion or timeout.

**Invariant dependency**: `blockingAcyclic` is the critical safety property,
integrated into `crossSubsystemInvariant` (CrossSubsystem.lean) as the 10th
predicate (AF1-B). Without it, this function's correctness guarantee degrades
from "complete chain walk" to "prefix of chain up to fuel limit".

**AI6-A (M-23) — Cycle behavior**: Under a cyclic blocking graph (invariant
violation), PIP propagation stops at the cycle boundary. Threads in the cycle
retain stale priority boosts until the cycle is broken by IPC completion or
timeout. This is conservative (not unsound): stale boosts cause over-promotion,
not under-promotion, so no priority inversion results. Formal cycle detection
and removal is recorded as a post-1.0 hardening candidate; no currently-active
plan file tracks it. -/
def blockingChain (st : SystemState) (tid : ThreadId) (fuel : Nat := st.objectIndex.length)
    : List ThreadId :=
  match fuel with
  | 0 => []
  | fuel' + 1 =>
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      match tcb.ipcState with
      | .blockedOnReply _ (some server) => server :: blockingChain st server fuel'
      | _ => []
    | _ => []

-- ============================================================================
-- D4-C4/C5: Helpers
-- ============================================================================

/-- D4-C4: Check if a thread appears in a chain. -/
def chainContains (chain : List ThreadId) (tid : ThreadId) : Bool :=
  chain.any (· == tid)

/-- D4-C5: All blocking graph edges (waiter, server) pairs. -/
def blockingGraphEdges (st : SystemState) : List (ThreadId × ThreadId) :=
  st.objectIndex.filterMap fun objId =>
    match st.objects[objId]? with
    | some (KernelObject.tcb tcb) =>
      match tcb.ipcState with
      | .blockedOnReply _ (some server) => some (tcb.tid, server)
      | _ => none
    | _ => none

-- ============================================================================
-- D4-D: Blocking graph acyclicity proofs
-- ============================================================================

/-- D4-D / AN5-B (SCH-M05): The IPC blocking relation is acyclic in a
well-formed system state. No thread can transitively block on itself via
Reply chains. This predicate is part of `crossSubsystemInvariant` (10th
conjunct, AF1-B). Fuel-bounded PIP propagation
(`propagatePriorityInheritance` uses `objectIndex.length` as fuel)
prevents non-termination, and chain-walk correctness depends on this
invariant being maintained by all ipcState-modifying operations.

**Naming disambiguation (AN5-B / SCH-M05)**: this predicate is **not**
the IPC-scope `SeLe4n.Kernel.tcbQueueChainAcyclic`
(`IPC/Invariant/Defs.lean:145`) even though both encode graph acyclicity:

* `blockingAcyclic` (this file) — acyclicity of the priority-inheritance
  **blocking graph** built by `blockingServer`: edge `tid → server`
  exists iff `tid` is blocked on a reply to `server`. Fuel bound:
  `objectIndex.length`. Consumed by PIP bounded-inversion and WCRT
  proofs.

* `tcbQueueChainAcyclic` (IPC scope) — acyclicity of the IPC **TCB
  queue-next chain** built by `TCB.queueNext`: edge `a → b` exists iff
  `a.queueNext = some b`. Consumed by the IPC `dualQueueSystemInvariant`
  and queue-membership preservation proofs.

The two predicates operate on different edge relations; a system can
satisfy one without the other. Proof authors importing both scheduler
and IPC hubs must keep them distinct. -/
def blockingAcyclic (st : SystemState) : Prop :=
  ∀ tid : ThreadId, tid ∉ blockingChain st tid

/-- D4-D3: Under blocking acyclicity, no thread appears in its own chain.
    This is a direct restatement of `blockingAcyclic` — retained for
    explicit naming in downstream proofs. -/
theorem blockingChain_acyclic (st : SystemState)
    (hAcyclic : blockingAcyclic st) (tid : ThreadId) :
    tid ∉ blockingChain st tid :=
  hAcyclic tid

/-- D4-D: Helper — the blocking chain server lookup for a given thread. -/
def blockingServer (st : SystemState) (tid : ThreadId) : Option ThreadId :=
  match st.objects[tid.toObjId]? with
  | some (KernelObject.tcb tcb) =>
    match tcb.ipcState with
    | .blockedOnReply _ (some server) => some server
    | _ => none
  | _ => none

-- ============================================================================
-- AK1-F (I-M04): PIP-boost / reply-blocked relation
-- ============================================================================

/-- AK1-F (I-M04 / MEDIUM): `blockingServer` returns `some _` IFF the thread's
    `ipcState` is `.blockedOnReply _ (some _)`. This is the structural
    characterization used by `timeoutThread` in `IPC/Operations/Timeout.lean`
    to decide whether to call `revertPriorityInheritance` — only threads
    on a reply-blocking chain have a blocking server to propagate PIP revert
    through.

    The `timeoutThread` PIP-revert path handles only `.blockedOnReply`
    (with `some serverId`). This lemma makes the discriminant formally
    precise: any thread *not* in `.blockedOnReply _ (some _)` has
    `blockingServer = none`, so no server to revert. -/
theorem blockingServer_isSome_iff_blockedOnReply_some
    (st : SystemState) (tid : ThreadId) :
    (blockingServer st tid).isSome ↔
    ∃ (tcb : TCB) (epId : SeLe4n.ObjId) (server : ThreadId),
      st.objects[tid.toObjId]? = some (.tcb tcb) ∧
      tcb.ipcState = .blockedOnReply epId (some server) := by
  constructor
  · intro hSome
    unfold blockingServer at hSome
    cases hObj : st.objects[tid.toObjId]? with
    | none => rw [hObj] at hSome; simp at hSome
    | some obj =>
      rw [hObj] at hSome
      cases obj with
      | tcb tcb =>
        simp only at hSome
        cases hIpc : tcb.ipcState with
        | blockedOnReply epId rt =>
          rw [hIpc] at hSome
          cases rt with
          | none => simp at hSome
          | some server =>
            -- cases hObj rewrote the goal's `st.objects[tid.toObjId]?` to `some (.tcb tcb)`
            exact ⟨tcb, epId, server, rfl, hIpc⟩
        | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnCall _
          | blockedOnNotification _ =>
          rw [hIpc] at hSome; simp at hSome
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
        | schedContext _ =>
        simp at hSome
  · rintro ⟨tcb, epId, server, hObj, hIpc⟩
    simp only [blockingServer, hObj, hIpc, Option.isSome_some]

/-- AK1-F (I-M04): Plan-named alias for the biconditional characterisation
    of `blockingServer`. The plan's nomenclature `pipBoost_attached_only_on_reply_blocked`
    captures the intent — PIP boost propagation (via `propagatePipBoost`
    walking the blocking graph) only follows chains anchored at a
    `.blockedOnReply _ (some server)` waiter. This alias makes the
    plan-suggested name callable. -/
abbrev pipBoost_attached_only_on_reply_blocked :=
  @blockingServer_isSome_iff_blockedOnReply_some

/-- AK1-F (I-M04): Specialized corollary — if `blockingServer st tid = some server`,
    then `tid` is in state `.blockedOnReply endpointId (some server)` for some
    endpoint. Used by `timeoutThread` to argue the PIP-revert call path is
    structurally identified by ipcState. -/
theorem blockingServer_some_implies_blockedOnReply
    (st : SystemState) (tid server : ThreadId)
    (h : blockingServer st tid = some server) :
    ∃ (tcb : TCB) (epId : SeLe4n.ObjId),
      st.objects[tid.toObjId]? = some (.tcb tcb) ∧
      tcb.ipcState = .blockedOnReply epId (some server) := by
  unfold blockingServer at h
  cases hObj : st.objects[tid.toObjId]? with
  | none => rw [hObj] at h; simp at h
  | some obj =>
    rw [hObj] at h
    cases obj with
    | tcb tcb =>
      simp only at h
      cases hIpc : tcb.ipcState with
      | blockedOnReply epId rt =>
        rw [hIpc] at h
        cases rt with
        | none => simp at h
        | some server' =>
          simp only [Option.some.injEq] at h
          subst h
          -- The cases on `st.objects[tid.toObjId]?` rewrote it to `some (.tcb tcb)` in the goal.
          exact ⟨tcb, epId, rfl, hIpc⟩
      | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnCall _
        | blockedOnNotification _ => rw [hIpc] at h; simp at h
    | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
      | schedContext _ => simp at h

-- ============================================================================
-- AF1-B5: Blocking graph frame lemmas
-- ============================================================================

/-- AF1-B5: Relate `blockingChain` to `blockingServer` for one step.
    This bridges the gap between the inline pattern match in `blockingChain`
    and the extracted `blockingServer` helper. -/
theorem blockingChain_step (st : SystemState) (tid : ThreadId) (n : Nat) :
    blockingChain st tid (n + 1) =
    match blockingServer st tid with
    | some server => server :: blockingChain st server n
    | none => [] := by
  cases hObj : st.objects[tid.toObjId]? with
  | none => simp [blockingChain, blockingServer, hObj]
  | some obj =>
    cases obj with
    | tcb tcb =>
      cases hIpc : tcb.ipcState with
      | blockedOnReply ep s =>
        cases s with
        | some server => simp [blockingChain, blockingServer, hObj, hIpc]
        | none => simp [blockingChain, blockingServer, hObj, hIpc]
      | ready => simp [blockingChain, blockingServer, hObj, hIpc]
      | blockedOnSend _ => simp [blockingChain, blockingServer, hObj, hIpc]
      | blockedOnReceive _ => simp [blockingChain, blockingServer, hObj, hIpc]
      | blockedOnNotification _ => simp [blockingChain, blockingServer, hObj, hIpc]
      | blockedOnCall _ => simp [blockingChain, blockingServer, hObj, hIpc]
    | endpoint _ => simp [blockingChain, blockingServer, hObj]
    | notification _ => simp [blockingChain, blockingServer, hObj]
    | cnode _ => simp [blockingChain, blockingServer, hObj]
    | vspaceRoot _ => simp [blockingChain, blockingServer, hObj]
    | untyped _ => simp [blockingChain, blockingServer, hObj]
    | schedContext _ => simp [blockingChain, blockingServer, hObj]

/-- AF1-B5: `blockingChain` is congruent in the blocking server function.
    If `blockingServer` returns the same results for all threads in both states,
    then `blockingChain` produces identical results for any fuel value. -/
theorem blockingChain_congr (st st' : SystemState) (tid : ThreadId) (fuel : Nat)
    (hServer : ∀ t, blockingServer st' t = blockingServer st t) :
    blockingChain st' tid fuel = blockingChain st tid fuel := by
  induction fuel generalizing tid with
  | zero => rfl
  | succ n ih =>
    rw [blockingChain_step, blockingChain_step, hServer]
    cases blockingServer st tid with
    | some server => exact congrArg (server :: ·) (ih server)
    | none => rfl

/-- AF1-B5: Frame lemma — if an operation preserves `blockingServer` for all
    threads and preserves `objectIndex`, then `blockingAcyclic` is preserved.
    This covers all 33 non-retype operations that do not modify any TCB's
    `ipcState` field. -/
theorem blockingAcyclic_frame
    (st st' : SystemState)
    (hPre : blockingAcyclic st)
    (hServer : ∀ tid, blockingServer st' tid = blockingServer st tid)
    (hObjIdx : st'.objectIndex = st.objectIndex) :
    blockingAcyclic st' := by
  intro tid hMem
  rw [show st'.objectIndex.length = st.objectIndex.length from congrArg List.length hObjIdx,
      blockingChain_congr st st' tid st.objectIndex.length hServer] at hMem
  exact hPre tid hMem

-- ============================================================================
-- D4-E: Blocking chain depth bound
-- ============================================================================

/-- D4-E: The blocking chain length is bounded by the fuel parameter.
Since default fuel = objectIndex.length, chain length ≤ total objects. -/
theorem blockingChain_length_le_fuel (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    (blockingChain st tid fuel).length ≤ fuel := by
  induction fuel generalizing tid with
  | zero => simp [blockingChain]
  | succ n ih =>
    simp only [blockingChain]
    match hObj : st.objects[tid.toObjId]? with
    | none => simp
    | some (KernelObject.tcb tcb) =>
      match hIpc : tcb.ipcState with
      | .blockedOnReply _ (some server) =>
        simp only [hIpc, List.length_cons]
        exact Nat.succ_le_succ (ih _)
      | .blockedOnReply _ none => simp_all
      | .ready => simp_all
      | .blockedOnSend _ => simp_all
      | .blockedOnReceive _ => simp_all
      | .blockedOnNotification _ => simp_all
      | .blockedOnCall _ => simp_all
    | some (KernelObject.endpoint _) => simp
    | some (KernelObject.notification _) => simp
    | some (KernelObject.cnode _) => simp
    | some (KernelObject.vspaceRoot _) => simp
    | some (KernelObject.untyped _) => simp
    | some (KernelObject.schedContext _) => simp

/-- D4-E: blockingChain with default fuel is bounded by objectIndex length. -/
theorem blockingChain_bounded (st : SystemState) (tid : ThreadId) :
    (blockingChain st tid st.objectIndex.length).length ≤ st.objectIndex.length :=
  blockingChain_length_le_fuel st tid st.objectIndex.length

/-- D4-E: Count of TCB objects in the system. -/
def countTCBs (st : SystemState) : Nat :=
  st.objectIndex.foldl (fun acc objId =>
    match st.objects[objId]? with
    | some (KernelObject.tcb _) => acc + 1
    | _ => acc) 0

end SeLe4n.Kernel.PriorityInheritance
