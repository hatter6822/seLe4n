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
# The notification donation's context-label check

A notification's scheduling context `sc` is lent to the thread `W` that takes
the notification's word only when **the context's label flows to `W`**
(`securityFlowsTo (ctx.objectLabelOf sc) (ctx.threadLabelOf W)`,
`donationContextFlows`); otherwise nothing is donated, which is seL4-MCS's own
"do nothing" branch of `maybeDonateSchedContext`.

The check reads static labels and the notification's context word, the word
seL4's own guard reads, and nothing else: it reads no reply object, no stack
and no other thread (`donationContextFlows_congr`).  A context can head a reply
stack (a thread bound to it called a server and lent it, and the server is
gone), and the reply to that stack's lender later takes the context back from
the thread it was lent to.  That is a flow from every lender on the stack to
`W`.  Where every lender `T` on a context's stack flows to the context's label
(`contextLendersFlow`), the check makes it one: `T ⊑ L(sc) ⊑ W`
(`donationContextFlows_lenders`), with no read of the stack.

The check is the checked kernel's, like every flow gate: it needs the
labelling context, so it lives in the wrapper
(`maybeDonateSchedContextFlowing`) the checked dispatch arms and the interrupt
entry call, and the ctx-free donation (`maybeDonateSchedContext`) stays seL4's.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The context-label check**: the label of the context the notification
lends (`notificationContext?`, seL4-MCS's `ntfnSchedContext`) flows to the thread the donation would lend it to; `true` where the
notification lends no context. -/
def donationContextFlows (ctx : LabelingContext) (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) : Bool :=
  match notificationContext? st n with
  | none => true
  | some s => securityFlowsTo (ctx.objectLabelOf s.toObjId) (ctx.threadLabelOf tid)

/-- **The checked notification donation**: seL4-MCS's `maybeDonateSchedContext`
where the context-label check passes, and nothing where it does not. -/
def maybeDonateSchedContextFlowing (ctx : LabelingContext) (st : SystemState)
    (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) : SystemState :=
  if donationContextFlows ctx st n tid then maybeDonateSchedContext st n tid else st

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

/-- **The decision reads the notification's context word and static labels,
nothing else**: two states whose notification names the same context give the
same answer, whatever either holds in any reply object, any stack or any other
thread.  This is the waiter-domain half of the decision's information-flow
argument: the labels are the policy's, and the context word is the field
seL4-MCS's own guard reads. -/
theorem donationContextFlows_congr {ctx : LabelingContext} {st st' : SystemState}
    {n : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    (h : notificationContext? st' n = notificationContext? st n) :
    donationContextFlows ctx st' n tid = donationContextFlows ctx st n tid := by
  unfold donationContextFlows; rw [h]

/-- **The check's guarantee**: where it passes, the label of the context the
notification lends flows to the thread it is lent to. -/
theorem donationContextFlows_context {ctx : LabelingContext} {st : SystemState}
    {n : SeLe4n.ObjId} {tid : SeLe4n.ThreadId} {s : SeLe4n.SchedContextId}
    (h : donationContextFlows ctx st n tid = true)
    (hS : notificationContext? st n = some s) :
    securityFlowsTo (ctx.objectLabelOf s.toObjId) (ctx.threadLabelOf tid) = true := by
  unfold donationContextFlows at h
  rw [hS] at h
  exact h

/-- **Where the check refuses, the checked donation writes nothing.** -/
theorem maybeDonateSchedContextFlowing_of_flows_false {ctx : LabelingContext}
    {st : SystemState} {n : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    (h : donationContextFlows ctx st n tid = false) :
    maybeDonateSchedContextFlowing ctx st n tid = st := by
  unfold maybeDonateSchedContextFlowing
  rw [h]; rfl

/-- **Where the check passes, the checked donation is seL4's.** -/
theorem maybeDonateSchedContextFlowing_of_flows {ctx : LabelingContext}
    {st : SystemState} {n : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    (h : donationContextFlows ctx st n tid = true) :
    maybeDonateSchedContextFlowing ctx st n tid = maybeDonateSchedContext st n tid := by
  unfold maybeDonateSchedContextFlowing
  rw [h]; rfl

/-- **The compiled checked donation**: the check, then the compiled donation
(`maybeDonateSchedContextFast`), so a lent context is written in place. -/
@[inline] def maybeDonateSchedContextFlowingFast (ctx : LabelingContext) (st : SystemState)
    (nCode tCode : Nat) : SystemState :=
  if donationContextFlows ctx st ⟨nCode⟩ ⟨tCode⟩ then maybeDonateSchedContextFast st nCode tCode
  else st

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
the same context (`notificationContext?`) under that context's policy, and the
two answers agree on a lifted context
(`donationContextFlowsGeneric_liftLegacyContext`). -/

/-- **The context-label check under a generic labelling context.** -/
def donationContextFlowsGeneric (gctx : GenericLabelingContext) (st : SystemState)
    (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) : Bool :=
  match notificationContext? st n with
  | none => true
  | some s => genericFlowCheck gctx (gctx.objectDomainOf s.toObjId) (gctx.threadDomainOf tid)

/-- **One question, one answer**: on a lifted legacy context the generic check
is the legacy one. -/
theorem donationContextFlowsGeneric_liftLegacyContext (ctx : LabelingContext)
    (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) :
    donationContextFlowsGeneric (liftLegacyContext ctx) st n tid =
      donationContextFlows ctx st n tid := by
  unfold donationContextFlowsGeneric donationContextFlows
  cases notificationContext? st n with
  | none => rfl
  | some s =>
    simp only [genericFlowCheck, domainFlowsTo, liftLegacyContext, legacyLattice_canFlow_embed]

/-- **The checked notification donation under a generic labelling context.** -/
def maybeDonateSchedContextFlowingGeneric (gctx : GenericLabelingContext) (st : SystemState)
    (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) : SystemState :=
  if donationContextFlowsGeneric gctx st n tid then maybeDonateSchedContext st n tid else st

/-- On a lifted legacy context it is the legacy checked donation. -/
theorem maybeDonateSchedContextFlowingGeneric_liftLegacyContext (ctx : LabelingContext)
    (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) :
    maybeDonateSchedContextFlowingGeneric (liftLegacyContext ctx) st n tid =
      maybeDonateSchedContextFlowing ctx st n tid := by
  unfold maybeDonateSchedContextFlowingGeneric maybeDonateSchedContextFlowing
  rw [donationContextFlowsGeneric_liftLegacyContext]

/-- **The generic checked donation is the donation or nothing.** -/
theorem maybeDonateSchedContextFlowingGeneric_induct (P : SystemState → Prop)
    (gctx : GenericLabelingContext) (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (hId : P st) (hDonate : P (maybeDonateSchedContext st n tid)) :
    P (maybeDonateSchedContextFlowingGeneric gctx st n tid) := by
  unfold maybeDonateSchedContextFlowingGeneric
  split
  · exact hDonate
  · exact hId


/-! ### The lenders on a context's stack

A context's reply stack is the chain of reply objects from its head
(`SchedContext.scReply`) down the `prev` links; each frame's caller lent the
context through a `Call`.  `contextLendersFlow` says every such lender flows to
the context's label; with it, the context-label check gives every lender on the
stack flowing to the thread the context is lent to
(`donationContextFlows_lenders`), with no read of the stack. -/

/-- **A reply object on a context's stack**: the head the context names, or a
frame below one on it (`Reply.prev`). -/
inductive OnContextStack (st : SystemState) (s : SeLe4n.SchedContextId) :
    SeLe4n.ReplyId → Prop where
  | head {sc : SchedContext} {r : SeLe4n.ReplyId} :
      st.getSchedContext? s = some sc → sc.scReply = some r → OnContextStack st s r
  | lower {r r' : SeLe4n.ReplyId} {rep : Reply} :
      OnContextStack st s r → st.getReply? r = some rep → rep.prev = some r' →
        OnContextStack st s r'

/-- **Every lender on a context's stack flows to the context's label**: the
caller of every reply object on the stack of every context. -/
def contextLendersFlow (ctx : LabelingContext) (st : SystemState) : Prop :=
  ∀ (s : SeLe4n.SchedContextId) (r : SeLe4n.ReplyId) (rep : Reply) (lender : SeLe4n.ThreadId),
    OnContextStack st s r → st.getReply? r = some rep → rep.caller = some lender →
      securityFlowsTo (ctx.threadLabelOf lender) (ctx.objectLabelOf s.toObjId) = true

/-- **A state whose contexts head no stack has no lender**: the predicate holds
outright (every boot state, every state before the first donating `Call`). -/
theorem contextLendersFlow_of_no_stacks (ctx : LabelingContext) (st : SystemState)
    (hNoHeads : ∀ (s : SeLe4n.SchedContextId) (sc : SchedContext),
      st.getSchedContext? s = some sc → sc.scReply = none) :
    contextLendersFlow ctx st := by
  intro s r rep lender hOn
  exfalso
  induction hOn with
  | head hSc hR => rw [hNoHeads _ _ hSc] at hR; cases hR
  | lower _ _ _ ih => exact ih

/-- **The lender flow the check delivers**: where the context-label check
passes and every lender on a context's stack flows to the context's label,
every lender on the stack of the context the notification lends flows to the
thread it is lent to.  The reply the lender later answers takes the context
back from that thread, so this is the flow the take-back is. -/
theorem donationContextFlows_lenders {ctx : LabelingContext} {st : SystemState}
    {n : SeLe4n.ObjId} {tid : SeLe4n.ThreadId} {s : SeLe4n.SchedContextId}
    (hInv : contextLendersFlow ctx st)
    (h : donationContextFlows ctx st n tid = true)
    (hS : notificationContext? st n = some s)
    {r : SeLe4n.ReplyId} {rep : Reply} {lender : SeLe4n.ThreadId}
    (hOn : OnContextStack st s r) (hRep : st.getReply? r = some rep)
    (hC : rep.caller = some lender) :
    securityFlowsTo (ctx.threadLabelOf lender) (ctx.threadLabelOf tid) = true :=
  securityFlowsTo_trans _ _ _ (hInv s r rep lender hOn hRep hC)
    (donationContextFlows_context h hS)

end SeLe4n.Kernel
