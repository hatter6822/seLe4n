-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.Core

/-!
# Setting a thread's spaces — seL4's `TCB_SetSpace`

**WS-BP BP7.1 (`v0.36.11`).**  A thread names the capability space it resolves
capability addresses in by its TCB's `cspaceRoot`, and the address space it runs
in by its `vspaceRoot`.  Until this module nothing wrote either field at
runtime: only the boot configured them, so the address spaces slice 4b carves
from untypeds (`untypedRetypeObject` at `CarveRequest.vspaceRoot`) could be
mapped into and reset but never run in.

`setThreadSpace` writes both, and nothing else, under three conditions the live
arm (`.tcbSetSpace`) establishes by capability before calling it:

* the target is **suspended** — its stored flag is `.Inactive` *and* the state
  itself classifies it so (`inferThreadState`: placed on no core, blocked on
  nothing).  Asking both means a stale flag cannot admit a thread the scheduler
  is running, whatever `threadInactiveFlagConsistent` says of the state.  A running or blocked thread's
  spaces are in use: its register frame, its in-flight IPC and — once BP7.2
  installs roots — the translation table a PE is walking are all read through
  them.  seL4 accepts `TCB_SetSpace` on a running thread and lets the change
  take effect at its next entry; this kernel asks the caller to suspend first,
  which is the order a manager configures a new thread in anyway (configure,
  then resume), and which keeps every invariant stated over a thread's roots
  from having to reason about a thread mid-flight;
* the new CSpace root is a **CNode**, and the new VSpace root a **VSpace root**
  — decided here against the store, not trusted of the resolver, so no thread
  is left with a root that names something else.

The write is one in-place rewrite of the TCB with the two fields replaced
(`rewriteObject`, under the witness its own lookup carries) — the shape
`setThreadFaultHandlerOp` writes, so the same bundle transport
(`insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull`) carries it.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **WS-BP BP7.1 (`v0.36.11`): set a suspended thread's CSpace and VSpace roots**
— seL4's `TCB_SetSpace`.  Refused, committing nothing, when the thread is not a
stored TCB (`.objectNotFound`), is not suspended (`.illegalState`), or either
root does not name an object of its kind (`.invalidCapability`).  The write is
the typed in-place rewrite under the lookup's own witness. -/
def setThreadSpace (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (cspaceRoot vspaceRoot : SeLe4n.ObjId) : Except KernelError SystemState :=
  match st.getTcbWitnessed? vtid.val with
  | none => .error .objectNotFound
  | some ⟨tcb, hTcb⟩ =>
    if tcb.threadState != .Inactive || inferThreadState st vtid.val tcb != .Inactive then
      .error .illegalState
    else if (st.getCNode? cspaceRoot).isNone then .error .invalidCapability
    else if (st.getVSpaceRoot? vspaceRoot).isNone then .error .invalidCapability
    else .ok (st.rewriteObject vtid.val.toObjId
      (.tcb { tcb with cspaceRoot := cspaceRoot, vspaceRoot := vspaceRoot })
      (SystemState.rewriteAdmissible_tcb hTcb _))

/-- **What a successful space change consists of**: the thread was a suspended
TCB, both roots name objects of their kind, and the state is the one TCB
rewrite. -/
theorem setThreadSpace_ok (st st' : SystemState) (vtid : SeLe4n.ValidThreadId)
    (cspaceRoot vspaceRoot : SeLe4n.ObjId)
    (h : setThreadSpace st vtid cspaceRoot vspaceRoot = .ok st') :
    ∃ tcb, st.getTcb? vtid.val = some tcb ∧ tcb.threadState = .Inactive ∧
      inferThreadState st vtid.val tcb = .Inactive ∧ (st.getCNode? cspaceRoot).isSome ∧ (st.getVSpaceRoot? vspaceRoot).isSome ∧
      st' = { st with objects := (st.objects.insert vtid.val.toObjId
        (.tcb { tcb with cspaceRoot := cspaceRoot, vspaceRoot := vspaceRoot })) } := by
  cases hT : st.getTcb? vtid.val with
  | none => simp [setThreadSpace, SystemState.getTcbWitnessed?_eq_none hT] at h
  | some tcb =>
    simp only [setThreadSpace, SystemState.getTcbWitnessed?_eq_some hT] at h
    by_cases hS : tcb.threadState = .Inactive ∧ inferThreadState st vtid.val tcb = .Inactive
    · have hB : (tcb.threadState != .Inactive || inferThreadState st vtid.val tcb != .Inactive)
          = false := by simp [hS.1, hS.2]
      cases hC : st.getCNode? cspaceRoot with
      | none => simp [hB, hC] at h
      | some cn =>
        cases hR : st.getVSpaceRoot? vspaceRoot with
        | none => simp [hB, hC, hR] at h
        | some root =>
          simp only [hB, hC, hR, Bool.false_eq_true, ↓reduceIte, Option.isNone_some,
            Except.ok.injEq] at h
          exact ⟨tcb, rfl, hS.1, hS.2, by simp, by simp, h.symm⟩
    · have : (tcb.threadState != .Inactive || inferThreadState st vtid.val tcb != .Inactive)
          = true := by
        by_cases h1 : tcb.threadState = .Inactive
        · have h2 : inferThreadState st vtid.val tcb ≠ .Inactive := fun h2 => hS ⟨h1, h2⟩
          simp [h2]
        · simp [h1]
      simp [this] at h

/-- **The payoff**: after a space change the thread's TCB names the two roots,
each an object of its kind in the pre-state, and every other field of it is
what it was. -/
theorem setThreadSpace_ok_tcb (st st' : SystemState) (vtid : SeLe4n.ValidThreadId)
    (cspaceRoot vspaceRoot : SeLe4n.ObjId) (hInv : st.objects.invExt)
    (h : setThreadSpace st vtid cspaceRoot vspaceRoot = .ok st') :
    ∃ tcb, st.getTcb? vtid.val = some tcb ∧ (st.getCNode? cspaceRoot).isSome ∧
      (st.getVSpaceRoot? vspaceRoot).isSome ∧
      st'.objects[vtid.val.toObjId]? =
        some (.tcb { tcb with cspaceRoot := cspaceRoot, vspaceRoot := vspaceRoot }) := by
  obtain ⟨tcb, hT, -, -, hC, hR, rfl⟩ := setThreadSpace_ok st st' vtid cspaceRoot vspaceRoot h
  exact ⟨tcb, hT, hC, hR, SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self _ _ _ hInv⟩

/-- A refused space change is refused for a stated reason: the thread must be
suspended.  A thread the state places on a core, or blocks, is refused
whatever its stored flag says — a running, ready or blocked thread's spaces are
in use. -/
theorem setThreadSpace_refuses_active (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (cspaceRoot vspaceRoot : SeLe4n.ObjId) (tcb : TCB)
    (hT : st.getTcb? vtid.val = some tcb)
    (hS : inferThreadState st vtid.val tcb ≠ .Inactive) :
    setThreadSpace st vtid cspaceRoot vspaceRoot = .error .illegalState := by
  have : (tcb.threadState != .Inactive || inferThreadState st vtid.val tcb != .Inactive)
      = true := by simp [hS]
  simp [setThreadSpace, SystemState.getTcbWitnessed?_eq_some hT, this]

end SeLe4n.Kernel
