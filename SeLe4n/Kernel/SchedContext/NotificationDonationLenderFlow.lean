-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.NotificationDonation
import SeLe4n.Kernel.InformationFlow.Policy

/-!
# The notification donation's lender flow check

A notification's scheduling context can head a reply stack: a thread `T` bound
to the context called a server and lent it, and the server is gone (deleted, or
it returned the context unanswered), so the context sits on `T`'s stack with no
holder.  seL4-MCS's `maybeDonateSchedContext` lends such a context to the
thread that takes the notification's word; the reply to `T` then takes it back
from that thread (`reply_remove`), so the replier deschedules the thread the
context was lent to.  That is a flow from `T`'s reply to the waiter, and the
checked kernel admits it only when it is one: **the notification donation lends
a context heading a stack only when the stack's top lender flows to the
waiter** (`donationLenderFlows`), and otherwise donates nothing, which is
seL4's own "do nothing" branch of the donation.

The check reads the top lender alone — the caller of the reply the context
heads (`notificationContextHeadLender?`).  Every lender below it flows to it,
because each one lent the context through a `Call` the flow gate admitted to the
lender above, so the top lender flowing to the waiter is every lender flowing to
it (`securityFlowsTo_trans`).

The check is the checked kernel's, like every flow gate: it needs the labelling
context, so it lives in the wrapper (`maybeDonateSchedContextFlowing`) the
checked dispatch arms and the interrupt entry call, and the ctx-free donation
(`maybeDonateSchedContext`) stays seL4's.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The top lender of the stack a notification's context heads**: the caller
of the reply at the head of the context's reply stack (`SchedContext.scReply`),
`none` where the notification has no context, the context heads no stack, or
the head reply names no caller. -/
def notificationContextHeadLender? (st : SystemState) (n : SeLe4n.ObjId) :
    Option SeLe4n.ThreadId :=
  match st.getNotification? n with
  | none => none
  | some ntfn =>
    match ntfn.schedContext with
    | none => none
    | some s =>
      match st.getSchedContext? s with
      | none => none
      | some sc =>
        match sc.scReply with
        | none => none
        | some r =>
          match st.getReply? r with
          | none => none
          | some rep => rep.caller

/-- **The lender flow check**: the top lender of the stack the notification's
context heads flows to the thread the donation would lend it to; `true` where
the context heads no stack. -/
def donationLenderFlows (ctx : LabelingContext) (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) : Bool :=
  match notificationContextHeadLender? st n with
  | none => true
  | some lender => securityFlowsTo (ctx.threadLabelOf lender) (ctx.threadLabelOf tid)

/-- **The checked notification donation**: seL4-MCS's `maybeDonateSchedContext`
where the lender flow check passes, and nothing where it does not. -/
def maybeDonateSchedContextFlowing (ctx : LabelingContext) (st : SystemState)
    (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) : SystemState :=
  if donationLenderFlows ctx st n tid then maybeDonateSchedContext st n tid else st

/-- **The checked donation is the donation or nothing.** -/
theorem maybeDonateSchedContextFlowing_cases (ctx : LabelingContext) (st : SystemState)
    (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) :
    maybeDonateSchedContextFlowing ctx st n tid = maybeDonateSchedContext st n tid ∨
      maybeDonateSchedContextFlowing ctx st n tid = st := by
  unfold maybeDonateSchedContextFlowing
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **A property the donation and the identity carry, the checked donation
carries.** -/
theorem maybeDonateSchedContextFlowing_induct (P : SystemState → Prop)
    (ctx : LabelingContext) (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (hId : P st) (hDonate : P (maybeDonateSchedContext st n tid)) :
    P (maybeDonateSchedContextFlowing ctx st n tid) := by
  rcases maybeDonateSchedContextFlowing_cases ctx st n tid with h | h <;> rw [h] <;> assumption
/-- **The check's guarantee**: where it passes, the stack's top lender flows to
the thread the context is lent to.  The notification-donation half of the
invariant that every lender on a stack flows to its holder. -/
theorem donationLenderFlows_lender {ctx : LabelingContext} {st : SystemState}
    {n : SeLe4n.ObjId} {tid lender : SeLe4n.ThreadId}
    (h : donationLenderFlows ctx st n tid = true)
    (hL : notificationContextHeadLender? st n = some lender) :
    securityFlowsTo (ctx.threadLabelOf lender) (ctx.threadLabelOf tid) = true := by
  unfold donationLenderFlows at h
  rw [hL] at h
  exact h

/-- **Where the check refuses, the checked donation writes nothing.** -/
theorem maybeDonateSchedContextFlowing_of_flows_false {ctx : LabelingContext}
    {st : SystemState} {n : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    (h : donationLenderFlows ctx st n tid = false) :
    maybeDonateSchedContextFlowing ctx st n tid = st := by
  unfold maybeDonateSchedContextFlowing
  rw [h]; rfl

/-- **Where the check passes, the checked donation is seL4's.** -/
theorem maybeDonateSchedContextFlowing_of_flows {ctx : LabelingContext}
    {st : SystemState} {n : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    (h : donationLenderFlows ctx st n tid = true) :
    maybeDonateSchedContextFlowing ctx st n tid = maybeDonateSchedContext st n tid := by
  unfold maybeDonateSchedContextFlowing
  rw [h]; rfl

/-- **The compiled checked donation**: the check, then the compiled donation
(`maybeDonateSchedContextFast`), so a lent context is written in place. -/
@[inline] def maybeDonateSchedContextFlowingFast (ctx : LabelingContext) (st : SystemState)
    (nCode tCode : Nat) : SystemState :=
  if donationLenderFlows ctx st ⟨nCode⟩ ⟨tCode⟩ then maybeDonateSchedContextFast st nCode tCode
  else st

/-- **The compiled checked donation is the checked donation.** -/
theorem maybeDonateSchedContextFlowingFast_eq (ctx : LabelingContext) (st : SystemState)
    (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) :
    maybeDonateSchedContextFlowingFast ctx st n.val tid.val =
      maybeDonateSchedContextFlowing ctx st n tid := by
  unfold maybeDonateSchedContextFlowingFast maybeDonateSchedContextFlowing
  rw [maybeDonateSchedContextFast_eq]

/-- …read on a thread named by its code. -/
theorem maybeDonateSchedContextFlowingFast_eq_code (ctx : LabelingContext) (st : SystemState)
    (n : SeLe4n.ObjId) (k : Nat) :
    maybeDonateSchedContextFlowingFast ctx st n.val k =
      maybeDonateSchedContextFlowing ctx st n ⟨k⟩ :=
  maybeDonateSchedContextFlowingFast_eq ctx st n ⟨k⟩

/-- The checked donation writes the object store and the scheduler alone. -/
theorem maybeDonateSchedContextFlowing_onlyObjectsSchedulerDiffer (ctx : LabelingContext)
    (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) :
    SystemState.onlyObjectsSchedulerDiffer (maybeDonateSchedContextFlowing ctx st n tid) st :=
  maybeDonateSchedContextFlowing_induct
    (fun s => SystemState.onlyObjectsSchedulerDiffer s st) ctx st n tid (.refl _)
    (maybeDonateSchedContext_onlyObjectsSchedulerDiffer st n tid)

/-- The checked donation keeps every thread's registers. -/
theorem maybeDonateSchedContextFlowing_registersAgree (ctx : LabelingContext)
    (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    registersAgree (maybeDonateSchedContextFlowing ctx st n tid) st :=
  maybeDonateSchedContextFlowing_induct (fun s => registersAgree s st) ctx st n tid
    (registersAgree.refl st) (maybeDonateSchedContext_registersAgree st n tid hInv)

/-! ### Under a generic labelling context

The declassifying signal runs under a generic labelling context (the legacy
context lifted, `liftLegacyContext`).  Its donation asks the same question of
the same lender (`notificationContextHeadLender?`) under that context's policy,
and the two answers agree on a lifted context
(`donationLenderFlowsGeneric_liftLegacyContext`). -/

/-- **The lender flow check under a generic labelling context.** -/
def donationLenderFlowsGeneric (gctx : GenericLabelingContext) (st : SystemState)
    (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) : Bool :=
  match notificationContextHeadLender? st n with
  | none => true
  | some lender => genericFlowCheck gctx (gctx.threadDomainOf lender) (gctx.threadDomainOf tid)

/-- **One question, one answer**: on a lifted legacy context the generic check
is the legacy one. -/
theorem donationLenderFlowsGeneric_liftLegacyContext (ctx : LabelingContext)
    (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) :
    donationLenderFlowsGeneric (liftLegacyContext ctx) st n tid = donationLenderFlows ctx st n tid := by
  unfold donationLenderFlowsGeneric donationLenderFlows
  cases notificationContextHeadLender? st n with
  | none => rfl
  | some lender =>
    simp only [genericFlowCheck, domainFlowsTo, liftLegacyContext, legacyLattice_canFlow_embed]

/-- **The checked notification donation under a generic labelling context.** -/
def maybeDonateSchedContextFlowingGeneric (gctx : GenericLabelingContext) (st : SystemState)
    (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) : SystemState :=
  if donationLenderFlowsGeneric gctx st n tid then maybeDonateSchedContext st n tid else st

/-- On a lifted legacy context it is the legacy checked donation. -/
theorem maybeDonateSchedContextFlowingGeneric_liftLegacyContext (ctx : LabelingContext)
    (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) :
    maybeDonateSchedContextFlowingGeneric (liftLegacyContext ctx) st n tid =
      maybeDonateSchedContextFlowing ctx st n tid := by
  unfold maybeDonateSchedContextFlowingGeneric maybeDonateSchedContextFlowing
  rw [donationLenderFlowsGeneric_liftLegacyContext]

/-- **The generic checked donation is the donation or nothing.** -/
theorem maybeDonateSchedContextFlowingGeneric_induct (P : SystemState → Prop)
    (gctx : GenericLabelingContext) (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (hId : P st) (hDonate : P (maybeDonateSchedContext st n tid)) :
    P (maybeDonateSchedContextFlowingGeneric gctx st n tid) := by
  unfold maybeDonateSchedContextFlowingGeneric
  split
  · exact hDonate
  · exact hId

end SeLe4n.Kernel
