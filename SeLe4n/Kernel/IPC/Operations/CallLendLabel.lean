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
(`contextLendersFlow`), the notification's context-label check gives every such
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
caller's context at the rendezvous, so it asks the call's own admission of the
thread it takes, the head of the endpoint's send queue, read on the state the
arm is handed.  `true` where no sender waits, since such a receive takes no
call and lends nothing either way. -/
def receiveLendAdmits (ctx : LabelingContext) (st : SystemState) (epId : SeLe4n.ObjId) : Bool :=
  match st.getEndpoint? epId with
  | some ep =>
      match ep.sendQ.head with
      | some s => callLendAdmits ctx st s
      | none => true
  | none => true

/-- The receive's admission is the call's admission of the send queue's head. -/
theorem receiveLendAdmits_of_head {ctx : LabelingContext} {st : SystemState}
    {epId : SeLe4n.ObjId} {ep : Endpoint} {s : SeLe4n.ThreadId}
    (hEp : st.getEndpoint? epId = some ep) (hHead : ep.sendQ.head = some s) :
    receiveLendAdmits ctx st epId = callLendAdmits ctx st s := by
  unfold receiveLendAdmits
  rw [hEp]
  simp only [hHead]

end SeLe4n.Kernel
