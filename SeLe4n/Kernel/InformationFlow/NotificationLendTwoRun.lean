-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.InformationFlow.LowEquivalencePairs
import SeLe4n.Kernel.SchedContext.NotificationDonationContextLabel

/-!
# The checked notification lend, in two runs

WS-SX SX9.1: the checked notification lend (`maybeDonateSchedContextFlowing`,
D30) made in two low-equivalent runs leaves them low-equivalent, for every
observer.  Its hypotheses: equal binding labels in both runs
(`bindingLabelsEqual`, D37), the two runs' agreement on the machine timer (the
context's release reads it, and the timer is outside the projection, covert
channel CC-2), and that each thread carries its own TCB's label
(`threadObjectLabelsEqual`, a fact of the labelling context that every
deployment context meets).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **Each thread carries its own TCB's label**: a fact of the labelling
context, not of a state.  `LabelingContextValid` asks only that a thread's label
flow to its TCB's; the lend's two-run theorem reads the waiter's binding words
off its TCB, so it needs the two equal. -/
def threadObjectLabelsEqual (ctx : LabelingContext) : Prop :=
  ∀ tid : SeLe4n.ThreadId, ctx.threadLabelOf tid = ctx.objectLabelOf tid.toObjId

/-- Every deployment context meets it. -/
theorem deploymentLabelingContext_threadObjectLabelsEqual (d : DeploymentLabeling) :
    threadObjectLabelsEqual (deploymentLabelingContext d) :=
  fun tid => (deploymentLabelingContext_thread_object_label_eq d tid).symm

section NotificationLendTwoRun

variable {ctx : LabelingContext} {observer : IfObserver}

/-- **The checked lend to a hidden thread is no view's**: the label check admits
only a context labelled as the thread is, so the context is hidden too. -/
theorem maybeDonateSchedContextFlowing_lowEquivalent_hidden (st : SystemState)
    (n : SeLe4n.ObjId) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hT : threadObservable ctx observer t = false)
    (hTo : objectObservable ctx observer t.toObjId = false) :
    lowEquivalent_smp ctx observer (maybeDonateSchedContextFlowing ctx st n t) st := by
  unfold maybeDonateSchedContextFlowing
  split
  · next hG =>
    refine maybeDonateSchedContext_lowEquivalent st n t hInv hT hTo (fun s hs => ?_)
    unfold donationContextFlows at hG
    rw [hs, twoWayLabelGate_iff_eq] at hG
    unfold objectObservable; rw [hG]; exact hT
  · exact lowEquivalent_smp_refl st

end NotificationLendTwoRun

end SeLe4n.Kernel
