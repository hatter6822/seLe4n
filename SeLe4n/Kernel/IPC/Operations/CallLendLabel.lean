-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Operations.Endpoint
import SeLe4n.Kernel.InformationFlow.Policy

/-!
# The call's lend admission

A `Call` to a passive server lends the caller's effective scheduling context
`s` (`callDonationSchedContext?`, bound or donated).  The checked kernel lends
it only where **the caller's label flows to the context's label**
(`callLendAdmits`); otherwise the call goes on and lends nothing, seL4-MCS's
"do nothing" branch of the donation (`applyCallDonationOnCoreWhen`).  The call
is never refused on this ground.

With every lender on a context's stack flowing to the context's label
(`lendingLabelsEqual`), the notification's context-label check gives every such
lender flowing to the thread the context is later lent to, with no read of the
stack (`donationContextFlows_lenders`).  This admission is what keeps that
predicate on a live trace: each push of a lender under a context is one of
these lends.

The admission reads static labels and the caller's own binding, nothing else
(`callLendAdmits_congr`): no receiver, no reply object, no other thread.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The lend admission**: the caller's label flows to the label of the
context it holds (bound or donated); `true` where it holds none, since such a
call lends nothing either way. -/
def callLendAdmits (ctx : LabelingContext) (st : SystemState) (caller : SeLe4n.ThreadId) : Bool :=
  match lookupTcb st caller with
  | some t =>
      match t.schedContextBinding.scId? with
      | some s => securityFlowsTo (ctx.threadLabelOf caller) (ctx.objectLabelOf s.toObjId)
      | none => true
  | none => true

/-- **The admission reads the caller's own binding and static labels, nothing
else**: two states in which the caller holds the same context give the same
answer, whatever either holds anywhere else. -/
theorem callLendAdmits_congr {ctx : LabelingContext} {st st' : SystemState}
    {caller : SeLe4n.ThreadId}
    (h : (lookupTcb st' caller).map (·.schedContextBinding.scId?) =
      (lookupTcb st caller).map (·.schedContextBinding.scId?)) :
    callLendAdmits ctx st' caller = callLendAdmits ctx st caller := by
  unfold callLendAdmits
  cases h1 : lookupTcb st' caller <;> cases h2 : lookupTcb st caller <;>
    simp only [h1, h2, Option.map_some, Option.map_none, Option.some.injEq,
      reduceCtorEq] at h ⊢
  rw [h]

/-- **The admission's guarantee**: where it passes and a call lends a context,
the caller's label flows to that context's label. -/
theorem callLendAdmits_flows {ctx : LabelingContext} {st : SystemState}
    {caller receiver : SeLe4n.ThreadId} {s : SeLe4n.SchedContextId}
    (hAdm : callLendAdmits ctx st caller = true)
    (hS : callDonationSchedContext? st caller receiver = some s) :
    securityFlowsTo (ctx.threadLabelOf caller) (ctx.objectLabelOf s.toObjId) = true := by
  unfold callDonationSchedContext? at hS
  unfold callLendAdmits at hAdm
  cases hR : lookupTcb st receiver with
  | none => simp only [hR, reduceCtorEq] at hS
  | some rt =>
    cases hB : rt.schedContextBinding with
    | bound _ => simp only [hR, hB, reduceCtorEq] at hS
    | donated _ _ => simp only [hR, hB, reduceCtorEq] at hS
    | unbound =>
      cases hC : lookupTcb st caller with
      | none => simp only [hR, hB, hC, reduceCtorEq] at hS
      | some ct =>
        simp only [hR, hB, hC] at hS
        simp only [hC, hS] at hAdm
        exact hAdm

/-- **The context the checked call lends**: the gated resolver at the
admission's answer lends only a context the caller flows to. -/
theorem callLendSchedContext?_flows {ctx : LabelingContext} {st : SystemState}
    {caller receiver : SeLe4n.ThreadId} {s : SeLe4n.SchedContextId}
    (hS : callLendSchedContext? (callLendAdmits ctx st caller) st caller receiver = some s) :
    securityFlowsTo (ctx.threadLabelOf caller) (ctx.objectLabelOf s.toObjId) = true := by
  unfold callLendSchedContext? at hS
  cases hAdm : callLendAdmits ctx st caller with
  | false => rw [hAdm] at hS; cases hS
  | true =>
    rw [hAdm] at hS
    exact callLendAdmits_flows hAdm hS

/-- **The receive's lend admission**: a receive that takes a `Call` lends the
caller's context at the rendezvous, so where the head of the endpoint's send
queue is blocked on a call it asks that call's own admission
(`callLendAdmits`), read on the state the arm is handed.  It refuses nothing
else: `true` where no thread waits, or where the head is blocked on a plain
send, since such a take lends nothing either way (ruling (y): the admission
refuses only what would lend). -/
def receiveLendAdmits (ctx : LabelingContext) (st : SystemState) (epId : SeLe4n.ObjId) : Bool :=
  match st.getEndpoint? epId with
  | some ep =>
      match ep.sendQ.head with
      | some s =>
          match lookupTcb st s with
          | some t =>
              match t.ipcState with
              | .blockedOnCall _ =>
                  match t.schedContextBinding.scId? with
                  | some sc => securityFlowsTo (ctx.threadLabelOf s) (ctx.objectLabelOf sc.toObjId)
                  | none => true
              | _ => true
          | none => true
      | none => true
  | none => true

/-- Where the send queue's head is blocked on a call, the receive's admission is
that call's admission. -/
theorem receiveLendAdmits_of_head {ctx : LabelingContext} {st : SystemState}
    {epId : SeLe4n.ObjId} {ep : Endpoint} {s : SeLe4n.ThreadId} {t : TCB} {e : SeLe4n.ObjId}
    (hEp : st.getEndpoint? epId = some ep) (hHead : ep.sendQ.head = some s)
    (hT : lookupTcb st s = some t) (hCall : t.ipcState = .blockedOnCall e) :
    receiveLendAdmits ctx st epId = callLendAdmits ctx st s := by
  unfold receiveLendAdmits callLendAdmits
  rw [hEp]
  simp only [hHead, hT, hCall]

/-- **The admission refuses only a call**: where it refuses, the send queue's
head is a thread blocked on a call holding a context its label does not flow
to. -/
theorem receiveLendAdmits_false {ctx : LabelingContext} {st : SystemState}
    {epId : SeLe4n.ObjId} (h : receiveLendAdmits ctx st epId = false) :
    ∃ (ep : Endpoint) (s : SeLe4n.ThreadId) (t : TCB) (e : SeLe4n.ObjId) (sc : SeLe4n.SchedContextId),
      st.getEndpoint? epId = some ep ∧ ep.sendQ.head = some s ∧ lookupTcb st s = some t ∧
      t.ipcState = .blockedOnCall e ∧ t.schedContextBinding.scId? = some sc ∧
      securityFlowsTo (ctx.threadLabelOf s) (ctx.objectLabelOf sc.toObjId) = false := by
  unfold receiveLendAdmits at h
  cases hEp : st.getEndpoint? epId with
  | none => simp only [hEp] at h; cases h
  | some ep =>
  simp only [hEp] at h
  cases hH : ep.sendQ.head with
  | none => simp only [hH] at h; cases h
  | some s =>
  simp only [hH] at h
  cases hT : lookupTcb st s with
  | none => simp only [hT] at h; cases h
  | some t =>
  simp only [hT] at h
  cases hI : t.ipcState with
  | blockedOnCall e =>
    simp only [hI] at h
    cases hS : t.schedContextBinding.scId? with
    | none => simp only [hS] at h; cases h
    | some sc =>
      simp only [hS] at h
      exact ⟨ep, s, t, e, sc, rfl, hH, hT, hI, hS, h⟩
  | _ => simp only [hI] at h; cases h

/-- The receive's admission passes wherever the call's admission of the send
queue's head passes. -/
theorem receiveLendAdmits_of_callLendAdmits {ctx : LabelingContext} {st : SystemState}
    {epId : SeLe4n.ObjId} {ep : Endpoint} {s : SeLe4n.ThreadId}
    (hEp : st.getEndpoint? epId = some ep) (hHead : ep.sendQ.head = some s)
    (hA : callLendAdmits ctx st s = true) :
    receiveLendAdmits ctx st epId = true := by
  cases h : receiveLendAdmits ctx st epId
  · obtain ⟨ep', s', t, e, sc, hEp', hH', hT, -, hS, hF⟩ := receiveLendAdmits_false h
    rw [hEp] at hEp'; cases hEp'
    rw [hHead] at hH'; cases hH'
    unfold callLendAdmits at hA
    simp only [hT, hS, hF] at hA
    cases hA
  · rfl

/-- **A Call lend's holder is at or below the lent context (D35's Call path).**
The endpoint gate is two-way, so a call's caller and the receiver that takes
it carry the endpoint's own label; the lend admission puts the caller at or
below the context it lends; so the receiver that comes to hold the context
satisfies `L(holder) ⊑ L(sc)`, and the context's budget charges and pops,
visible at its label, are at a label the holder may write. -/
theorem callLend_holderFlowsToContext {ctx : LabelingContext} {st : SystemState}
    {epId : SeLe4n.ObjId} {caller receiver : SeLe4n.ThreadId} {s : SeLe4n.SchedContextId}
    (hSend : endpointFlowGate ctx epId (ctx.threadLabelOf caller) (ctx.endpointLabelOf epId) = true)
    (hRecv : endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf receiver) = true)
    (hAdm : callLendAdmits ctx st caller = true)
    (hS : callDonationSchedContext? st caller receiver = some s) :
    securityFlowsTo (ctx.threadLabelOf receiver) (ctx.objectLabelOf s.toObjId) = true := by
  have hC := endpointFlowGate_implies_eq ctx epId _ _ hSend
  have hR := endpointFlowGate_implies_eq ctx epId _ _ hRecv
  rw [← hR, ← hC]
  exact callLendAdmits_flows hAdm hS

end SeLe4n.Kernel
