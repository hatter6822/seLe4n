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
and recurse. Terminates when fuel exhausted or thread not in blockedOnReply. -/
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

/-- D4-D: The IPC blocking relation is acyclic in a well-formed system state.
This is derivable from the IPC queue chain acyclicity invariant:
no thread can transitively block on itself via Reply chains. -/
def blockingAcyclic (st : SystemState) : Prop :=
  ∀ tid : ThreadId, tid ∉ blockingChain st tid

/-- D4-D3: Under blocking acyclicity, no thread appears in its own chain. -/
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
