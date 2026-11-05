/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.DeliveredInPlace
import SeLe4n.Kernel.IPC.Operations.DonationInPlace

/-!
# A donating call, each object written in its slot

seL4-MCS's `sendIPC` on a call to a passive server: the rendezvous, then
`schedContext_donate` and `reply_push` (`donateSchedContext`), then the priority
walk.  When every check of the rendezvous and of the donation passes on the
pre-state, each write lands in its slot (`donateSchedContextInPlace`), the
replenishment migration between the donor's and the server's home cores moves
the context's release link in its slot (`migrateSchedContextReplenishment`,
compiled as `migrateReplenishmentWrite`), and a message of at most four words is
written straight into the server's registers (`performCallDonatingDelivered`):
the call builds no object, no message and no table, on one core or across two.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section MessageSlots

variable (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
  (μ : Option IpcMessage → Option IpcMessage) (π : Nat → Nat)

theorem hasSufficientBudget_msg (st : SystemState) (t : TCB) :
    hasSufficientBudget (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) t =
      hasSufficientBudget st t := by
  unfold hasSufficientBudget
  simp only [SystemState.getSchedContext?_mapTcbInPlace]

theorem hasSufficientBudget_withMessageSlots (st : SystemState) (t : TCB) :
    hasSufficientBudget st (TCB.withMessageSlots ρ μ π t) = hasSufficientBudget st t := rfl

theorem markCandidacyGainFor_msg (st : SystemState) (tid : SeLe4n.ThreadId) (e : Bool) :
    markCandidacyGainFor (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) tid e =
      (markCandidacyGainFor st tid e).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  unfold markCandidacyGainFor
  split
  · rfl
  · rcases getTcb?_msg_cases r ρ μ π st tid with h | ⟨_, h⟩ <;> rw [h]
    · cases st.getTcb? tid with
      | none => rfl
      | some t =>
        simp only [hasSufficientBudget_msg]
        split
        · exact markKeyFlagsOver_msg r ρ μ π st _ _ _ _
        · rfl
    · cases st.getTcb? tid with
      | none => rfl
      | some t =>
        simp only [Option.map_some, hasSufficientBudget_msg, hasSufficientBudget_withMessageSlots,
          TCB.withMessageSlots_runCoreCode]
        split
        · exact markKeyFlagsOver_msg r ρ μ π st _ _ _ _
        · rfl

theorem updateSchedContext_msg (st : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hNo : st.objects.noResizeDue) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).updateSchedContext scId f =
      (st.updateSchedContext scId f).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [SystemState.updateSchedContext_eq_impl]
  unfold SystemState.updateSchedContextImpl
  rw [SystemState.getSchedContext?_mapTcbInPlace]
  split
  · exact modifyObject_msg r ρ μ st _ _ hNo (fun o => by cases o <;> rfl)
  · rfl

theorem lookupTcb_msg (st : SystemState) (x : SeLe4n.ThreadId) (hx : r ≠ x) :
    lookupTcb (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) x = lookupTcb st x := by
  unfold lookupTcb
  rw [SystemState.getTcb?_mapTcbInPlace, if_neg hx]

end MessageSlots

theorem updateSchedContext_noResizeDue (st : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hNo : st.objects.noResizeDue) :
    (st.updateSchedContext scId f).objects.noResizeDue := by
  rw [SystemState.updateSchedContext_eq_impl]
  unfold SystemState.updateSchedContextImpl
  split
  · exact modifyObject_noResizeDue _ _ _ hNo
  · exact hNo

/-- The donation leaves the table's size and capacity alone. -/
theorem donateSchedContextInPlace_noResizeDue (st : SystemState) (client server : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (hNo : st.objects.noResizeDue) :
    (donateSchedContextInPlace st client server scId).objects.noResizeDue := by
  unfold donateSchedContextInPlace
  split
  · exact hNo
  · split
    · exact hNo
    · split
      · exact hNo
      · split
        · exact hNo
        · split
          · exact hNo
          · dsimp only
            rw [markKeyChangeParts_objects, markCandidacyGainFor_objects, markKeyChangeParts_objects,
              markCandidacyGainFor_objects]
            refine updateTcb_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _ ?_)
            split <;> (repeat (first | exact hNo | apply modifyObject_noResizeDue |
              apply updateSchedContext_noResizeDue))

/-- **The donation commutes with a delivery** to a thread other than the donor. -/
theorem donateSchedContextInPlace_msg (r : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat) (st : SystemState) (client server : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (hNo : st.objects.noResizeDue) (hC : r ≠ client) :
    donateSchedContextInPlace (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) client server scId =
      (donateSchedContextInPlace st client server scId).mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  unfold donateSchedContextInPlace
  simp only [SystemState.getSchedContext?_mapTcbInPlace, SystemState.getReply?_mapTcbInPlace,
    lookupTcb_msg r ρ μ π st client hC, effectiveDeadline_msg, hasSufficientBudget_msg]
  cases st.getSchedContext? scId with
  | none => rfl
  | some sc =>
    cases lookupTcb st client with
    | none => rfl
    | some donor =>
      try dsimp only
      cases donor.replyObjectCode with
      | zero => rfl
      | succ k =>
        try dsimp only
        cases st.getReply? ⟨k⟩ with
        | none => rfl
        | some pr =>
          try dsimp only
          cases sc.scReply with
          | none =>
            rcases getTcb?_msg_cases r ρ μ π st server with h | ⟨_, h⟩ <;> rw [h] <;>
              cases st.getTcb? server <;> (try simp only [Option.map_none]) <;>
              try (with_reducible rfl)
            all_goals
              try simp only [Option.map_some, TCB.withMessageSlots_boostedPriority,
                TCB.withMessageSlots_domain, effectiveDeadline_withMessageSlots,
                hasSufficientBudget_withMessageSlots]
              try dsimp only
              rw [updateSchedContext_msg r ρ μ π _ _ _ hNo,
                modifyObject_msg r ρ μ _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo)
                  (fun o => by cases o <;> rfl),
                updateTcb_msg r ρ μ π _ client _ ?_ (fun h => absurd h hC.symm),
                updateTcb_msg r ρ μ π _ server _ ?_ ?_,
                markCandidacyGainFor_msg, markKeyChangeParts_msg, markCandidacyGainFor_msg,
                markKeyChangeParts_msg]
            all_goals (repeat (first | exact hNo | with_reducible apply updateTcb_noResizeDue |
              with_reducible apply modifyObject_noResizeDue |
              with_reducible apply updateSchedContext_noResizeDue | (intro _ _; rfl)))
          | some old =>
            rcases getTcb?_msg_cases r ρ μ π st server with h | ⟨_, h⟩ <;> rw [h] <;>
              cases st.getTcb? server <;> (try simp only [Option.map_none]) <;>
              try (with_reducible rfl)
            all_goals
              try simp only [Option.map_some, TCB.withMessageSlots_boostedPriority,
                TCB.withMessageSlots_domain, effectiveDeadline_withMessageSlots,
                hasSufficientBudget_withMessageSlots]
              try dsimp only
              rw [updateSchedContext_msg r ρ μ π _ _ _ hNo,
                modifyObject_msg r ρ μ _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo)
                  (fun o => by cases o <;> rfl),
                modifyObject_msg r ρ μ _ _ _ ?_ (fun o => by cases o <;> rfl),
                updateTcb_msg r ρ μ π _ client _ ?_ (fun h => absurd h hC.symm),
                updateTcb_msg r ρ μ π _ server _ ?_ ?_,
                markCandidacyGainFor_msg, markKeyChangeParts_msg, markCandidacyGainFor_msg,
                markKeyChangeParts_msg]
            all_goals (repeat (first | exact hNo | with_reducible apply updateTcb_noResizeDue |
              with_reducible apply modifyObject_noResizeDue |
              with_reducible apply updateSchedContext_noResizeDue | (intro _ _; rfl)))

section ReleaseMoves
variable (r : SeLe4n.ThreadId) (g : TCB → TCB)

/-- A context written in its slot commutes with a thread written in its slot. -/
theorem mapSchedContextInPlace_mapTcbInPlace (st : SystemState) (s : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) :
    (st.mapTcbInPlace r g).mapSchedContextInPlace s f =
      (st.mapSchedContextInPlace s f).mapTcbInPlace r g :=
  SystemState.mapTcbInPlace_swap_objects st r g _ _ (fun _ o => by cases o <;> rfl)

theorem releaseNextOn_mapTcbInPlace (st : SystemState) :
    (st.mapTcbInPlace r g).releaseNextOn = st.releaseNextOn := by
  funext c s; unfold SystemState.releaseNextOn; rw [SystemState.getSchedContext?_mapTcbInPlace]

theorem releaseAtOn_mapTcbInPlace (st : SystemState) :
    (st.mapTcbInPlace r g).releaseAtOn = st.releaseAtOn := by
  funext c s; unfold SystemState.releaseAtOn; rw [SystemState.getSchedContext?_mapTcbInPlace]

theorem releaseQueuedOn_mapTcbInPlace (st : SystemState) :
    (st.mapTcbInPlace r g).releaseQueuedOn = st.releaseQueuedOn := by
  funext c s; unfold SystemState.releaseQueuedOn; rw [SystemState.getSchedContext?_mapTcbInPlace]

theorem releaseQueuedAnywhere_mapTcbInPlace (st : SystemState) (s : SeLe4n.SchedContextId) :
    (st.mapTcbInPlace r g).releaseQueuedAnywhere s = st.releaseQueuedAnywhere s := by
  unfold SystemState.releaseQueuedAnywhere; rw [SystemState.getSchedContext?_mapTcbInPlace]

theorem releaseUnlinkOn_mapTcbInPlace (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    (st.mapTcbInPlace r g).releaseUnlinkOn c s = (st.releaseUnlinkOn c s).mapTcbInPlace r g := by
  unfold SystemState.releaseUnlinkOn
  simp only [releaseQueuedOn_mapTcbInPlace, SystemState.releasePredOf_eq,
    releaseNextOn_mapTcbInPlace, SystemState.mapTcbInPlace_scheduler,
    mapSchedContextInPlace_mapTcbInPlace]
  split
  · split <;> rfl
  · rfl

theorem releaseLinkIn_mapTcbInPlace (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) :
    (st.mapTcbInPlace r g).releaseLinkIn c s t = (st.releaseLinkIn c s t).mapTcbInPlace r g := by
  unfold SystemState.releaseLinkIn
  simp only [SystemState.releasePredBefore_eq, releaseNextOn_mapTcbInPlace,
    releaseAtOn_mapTcbInPlace, SystemState.mapTcbInPlace_scheduler,
    mapSchedContextInPlace_mapTcbInPlace]
  split <;> rfl

theorem releaseRemoveOn_mapTcbInPlace (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    (st.mapTcbInPlace r g).releaseRemoveOn c s = (st.releaseRemoveOn c s).mapTcbInPlace r g := by
  unfold SystemState.releaseRemoveOn
  rw [releaseUnlinkOn_mapTcbInPlace]; rfl

theorem releaseInsertOn_mapTcbInPlace (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) :
    (st.mapTcbInPlace r g).releaseInsertOn c s t = (st.releaseInsertOn c s t).mapTcbInPlace r g := by
  unfold SystemState.releaseInsertOn
  rw [releaseQueuedAnywhere_mapTcbInPlace, SystemState.getSchedContext?_mapTcbInPlace]
  split
  · rfl
  · unfold SystemState.releaseInsertFresh
    rw [releaseLinkIn_mapTcbInPlace]; rfl

/-- **The replenishment migration commutes with a thread written in its slot**:
it moves a context's release link and the ghost queues, and reads no thread. -/
theorem migrateSchedContextReplenishment_mapTcbInPlace (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore : CoreId) :
    migrateSchedContextReplenishment (st.mapTcbInPlace r g) scId fromCore toCore =
      (migrateSchedContextReplenishment st scId fromCore toCore).mapTcbInPlace r g := by
  unfold migrateSchedContextReplenishment
  split
  · rfl
  · rw [releaseQueuedOn_mapTcbInPlace, releaseAtOn_mapTcbInPlace]
    dsimp only
    split
    · rw [releaseRemoveOn_mapTcbInPlace, releaseInsertOn_mapTcbInPlace]; rfl
    · rfl

end ReleaseMoves

theorem releaseUnlinkOn_noResizeDue (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (hNo : st.objects.noResizeDue) : (st.releaseUnlinkOn c s).objects.noResizeDue := by
  unfold SystemState.releaseUnlinkOn
  split
  · dsimp only; split <;> exact hNo
  · exact hNo

theorem releaseLinkIn_noResizeDue (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) (hNo : st.objects.noResizeDue) : (st.releaseLinkIn c s t).objects.noResizeDue := by
  unfold SystemState.releaseLinkIn
  dsimp only; split <;> exact hNo

/-- The migration leaves the table's size and capacity alone. -/
theorem migrateSchedContextReplenishment_noResizeDue (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore : CoreId) (hNo : st.objects.noResizeDue) :
    (migrateSchedContextReplenishment st scId fromCore toCore).objects.noResizeDue := by
  unfold migrateSchedContextReplenishment
  split
  · exact hNo
  · dsimp only
    split
    · show ((st.releaseRemoveOn fromCore scId).releaseInsertOn toCore scId _).objects.noResizeDue
      unfold SystemState.releaseInsertOn
      split
      · exact releaseUnlinkOn_noResizeDue _ _ _ hNo
      · exact releaseLinkIn_noResizeDue _ _ _ _ (releaseUnlinkOn_noResizeDue _ _ _ hNo)
    · exact hNo

/-- **The donation a call makes, checked before any write**: an unbound
receiver, a caller holding a context it is the bound thread of, the context's
slot local, and the frame below it, if any, another reply whose slot is local.
Read off the codes, so the test builds nothing.  Donor and server may be homed
on different cores: the replenishment migration moves the context's release
link in its slot whatever the cores. -/
@[inline] def callDonationReady (st : SystemState) (caller r : SeLe4n.ThreadId) (ct rt : TCB)
    (rid : SeLe4n.ReplyId) : Bool :=
  rt.scBindingScCode == 0 &&
  (match ct.scBindingScCode with
   | 0 => false
   | k + 1 =>
     storeLeavesIndexAndTypes st (SeLe4n.SchedContextId.toObjId ⟨k⟩) .schedContext &&
     st.objects.findsInPlace (SeLe4n.SchedContextId.toObjId ⟨k⟩) &&
     (match st.getSchedContext? ⟨k⟩ with
      | some sc => sc.boundThreadCode == caller.val + 1 &&
          (match sc.scReply with
           | none => true
           | some old => old != rid &&
               storeLeavesIndexAndTypes st old.toObjId .reply &&
               st.objects.findsInPlace old.toObjId &&
               (st.getReply? old).isSome)
      | none => false))

/-- **A donating call writes only its slots**: the rendezvous's
(`callTakesReplyInPlace`) and the donation's (`callDonationReady`). -/
@[inline] def callDonatesInPlace (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (rt : TCB) (rid : SeLe4n.ReplyId) : Bool :=
  callTakesReplyInPlace st endpointId caller r rt rid &&
  (match st.getTcb? caller with
   | some ct => callDonationReady st caller r ct rt rid
   | none => false)

/-- The context a caller runs on, read off its binding's code. -/
@[inline] def callerScId (st : SystemState) (caller : SeLe4n.ThreadId) : SeLe4n.SchedContextId :=
  match st.getTcb? caller with
  | some ct => ⟨ct.scBindingScCode - 1⟩
  | none => ⟨0⟩

/-- The donating call's state after the server's priority walk: the
rendezvous, the donation, the replenishment migration from the donor's home
core to the server's (`donorHome`, `doneeHome`, read off the pre-state), the
walk, each write in its slot. -/
@[noinline] def performCallDonating (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (scId : SeLe4n.SchedContextId) (donorHome doneeHome : Concurrency.CoreId)
    (msg : IpcMessage) (core : Concurrency.CoreId) : SystemState :=
  (PriorityInheritance.propagatePipChainCrossCore
    (migrateSchedContextReplenishment
      (donateSchedContextInPlace (storeCallRendezvous st endpointId caller r next rid msg core)
        caller r scId) scId donorHome doneeHome) r core).1

/-- **The donating call, delivered**: the server woken without the message, the
donation, the priority walk, then the message's frame written into the server's
saved registers. -/
@[noinline] def performCallDonatingDelivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (nextCode : Nat) (rid : SeLe4n.ReplyId)
    (scId : SeLe4n.SchedContextId) (donorHome doneeHome : Concurrency.CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool)
    (core : Concurrency.CoreId) : SystemState :=
  let X := (PriorityInheritance.propagatePipChainCrossCore
    (migrateSchedContextReplenishment
      (donateSchedContextInPlace (storeCallRendezvousReady st endpointId caller r nextCode rid core)
        caller r scId) scId donorHome doneeHome) r core).1
  writeDeliveredFrameIfReady X r (Architecture.regMessageFrameW layout rf len badgeWord badged)
    (fun _ => holdDeliveredBody X r layout rf len (SeLe4n.Badge.opt badgeWord badged))

/-- A donating call carrying more than four words: held and staged as the
specification does, out of line. -/
@[noinline] def callDonatingStaged (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (nextCode : Nat) (rid : SeLe4n.ReplyId)
    (scId : SeLe4n.SchedContextId) (donorHome doneeHome : Concurrency.CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge)
    (core : Concurrency.CoreId) : SystemState :=
  Architecture.stageWokenDelivery
    (performCallDonating st endpointId caller r (ThreadId.ofOptCode nextCode) rid scId donorHome
      doneeHome { registers := Architecture.regMessageBody layout rf len, badge := badge } core)
    (some r) 0

/-- The checked call arm's donating rendezvous: delivered for a message of at
most four words, staged otherwise. -/
@[inline] def callRendezvousDonatingDelivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (nextCode : Nat) (rid : SeLe4n.ReplyId)
    (scId : SeLe4n.SchedContextId) (donorHome doneeHome : Concurrency.CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool)
    (core : Concurrency.CoreId) : SystemState :=
  if Architecture.regMessageLength layout len ≤ 4 then
    performCallDonatingDelivered st endpointId caller r nextCode rid scId donorHome doneeHome layout
      rf len badgeWord badged core
  else callDonatingStaged st endpointId caller r nextCode rid scId donorHome doneeHome layout rf
    len (SeLe4n.Badge.opt badgeWord badged) core

/-- **The staged donating call is the delivered one** for a message of at most
four words. -/
theorem stageWokenDelivery_performCallDonating (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (scId : SeLe4n.SchedContextId) (donorHome doneeHome : Concurrency.CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool)
    (core : Concurrency.CoreId) (hNo : st.objects.noResizeDue) (hNe : caller ≠ r)
    (hSz : Architecture.regMessageLength layout len ≤ 4) :
    Architecture.stageWokenDelivery
        (performCallDonating st endpointId caller r next rid scId donorHome doneeHome
          { registers := Architecture.regMessageBody layout rf len,
            badge := SeLe4n.Badge.opt badgeWord badged } core)
        (some r) 0 =
      performCallDonatingDelivered st endpointId caller r (ThreadId.optCode next) rid scId
        donorHome doneeHome layout rf len badgeWord badged core := by
  have hNoS := storeCallRendezvousReady_noResizeDue st endpointId caller r
    (ThreadId.optCode next) rid core hNo
  have hNoD := migrateSchedContextReplenishment_noResizeDue _ scId donorHome doneeHome
    (donateSchedContextInPlace_noResizeDue _ caller r scId hNoS)
  unfold performCallDonating performCallDonatingDelivered
  rw [Architecture.regMessageFrameW_eq, storeCallRendezvous_eq_hold _ _ _ _ _ _ _ _ hNo hNe,
    donateSchedContextInPlace_msg _ _ _ _ _ _ _ _ hNoS (Ne.symm hNe),
    migrateSchedContextReplenishment_mapTcbInPlace,
    propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoD, Architecture.stageWokenDelivery_some,
    stageDeliveredMessage_holdMessage _ _ _ (propagatePipChainCrossCore_noResizeDue _ _ _ hNoD)
      (by rw [Architecture.regMessageBody_size]; exact hSz),
    Architecture.returnFrameOfMessage_regMessageBody]
  rfl

theorem callTakesReplyInPlace_noResizeDue {st : SystemState} {endpointId : SeLe4n.ObjId}
    {caller r : SeLe4n.ThreadId} {rt : TCB} {rid : SeLe4n.ReplyId}
    (h : callTakesReplyInPlace st endpointId caller r rt rid = true) : st.objects.noResizeDue := by
  simp only [callTakesReplyInPlace, sendWakesInPlace, Bool.and_eq_true] at h
  exact RHTable.noResizeDue_of_findsInPlace h.1.1.1.1.1.1.1.1.1.1.1.1.2

theorem callTakesReplyInPlace_ne {st : SystemState} {endpointId : SeLe4n.ObjId}
    {caller r : SeLe4n.ThreadId} {rt : TCB} {rid : SeLe4n.ReplyId}
    (h : callTakesReplyInPlace st endpointId caller r rt rid = true) : caller ≠ r := by
  simp only [callTakesReplyInPlace, Bool.and_eq_true] at h
  exact bne_iff_ne.mp h.1.1.1.1.1.1.1.2

theorem callRendezvousDonatingDelivered_eq (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (rt : TCB) (rid : SeLe4n.ReplyId)
    (scId : SeLe4n.SchedContextId) (donorHome doneeHome : Concurrency.CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool)
    (core : Concurrency.CoreId) (hG : callDonatesInPlace st endpointId caller r rt rid = true) :
    callRendezvousDonatingDelivered st endpointId caller r rt.queueNextCode rid scId donorHome
        doneeHome layout rf len badgeWord badged core =
      Architecture.stageWokenDelivery
        (performCallDonating st endpointId caller r rt.queueNext rid scId donorHome doneeHome
          { registers := Architecture.regMessageBody layout rf len,
            badge := SeLe4n.Badge.opt badgeWord badged } core)
        (some r) 0 := by
  simp only [callDonatesInPlace, Bool.and_eq_true] at hG
  unfold callRendezvousDonatingDelivered
  split
  · next hSz =>
    rw [← TCB.optCode_queueNext]
    exact (stageWokenDelivery_performCallDonating _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (callTakesReplyInPlace_noResizeDue hG.1) (callTakesReplyInPlace_ne hG.1) hSz).symm
  · unfold callDonatingStaged
    rw [← TCB.optCode_queueNext, SeLe4n.ThreadId.ofOptCode_optCode]

/-- **The checked donating call dispatch, in place**: under the flow gate and
`callDonatesInPlace`, a call that finds a passive server and transfers no
capability commits `performCallDonating`'s state with an empty transfer
summary: the rendezvous, `schedContext_donate` and `reply_push` each in its
slot, the replenishment migrated from the donor's home core to the server's
(both read off the pre-state, as the dispatch reads them), then the priority
walk. -/
theorem callDispatchChecked_donating_inPlace (ctx : LabelingContext) (st : SystemState)
    (endpointId : SeLe4n.ObjId) (ep : Endpoint) (caller r : SeLe4n.ThreadId) (rt : TCB)
    (rid : SeLe4n.ReplyId) (payload : SendPayload) (msg : IpcMessage) (slot : SeLe4n.Slot)
    (core : Concurrency.CoreId)
    (hM : sendPayloadMessage st caller payload = msg)
    (hReq : sendCapRequest st endpointId caller payload = none)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.receiveQ.head = some r)
    (hT : st.objects[r.toObjId]? = some (.tcb rt)) (hRid : rt.pendingReceiveReply = some rid)
    (hG : callDonatesInPlace st endpointId caller r rt rid = true)
    (hFlow : endpointFlowGate ctx endpointId (ctx.threadLabelOf caller)
      (ctx.endpointLabelOf endpointId) = true) :
    ∃ sgi, endpointCallCrossCoreDispatchChecked ctx endpointId caller payload slot core st =
      (performCallDonating st endpointId caller r rt.queueNext rid (callerScId st caller)
        (determineTargetCore st caller) (determineTargetCore st r) msg core,
       .ok ({ results := #[] }, sgi)) := by
  simp only [callDonatesInPlace, Bool.and_eq_true] at hG
  obtain ⟨hTR, hDR⟩ := hG
  have hTR' := hTR
  simp only [callTakesReplyInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hTR'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hSG, hCRes⟩, -⟩, -⟩, hLC⟩, hFC⟩, hLR⟩, hFR⟩, -⟩, hRp⟩ := hTR'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨hRRes, -⟩, -⟩, hLH⟩, -⟩, -⟩ := hSG'
  split at hDR
  case h_2 => cases hDR
  rename_i ct hCo
  split at hRp
  case h_2 => cases hRp
  rename_i rp hRp0
  have hFree := hRp
  simp only [Reply.isFree, Bool.and_eq_true, Option.isNone_iff_eq_none] at hFree
  obtain ⟨⟨-, hRpPrev⟩, hRpNext⟩ := hFree
  unfold callDonationReady at hDR
  rw [Bool.and_eq_true, beq_iff_eq] at hDR
  obtain ⟨hRB, hDR⟩ := hDR
  obtain ⟨k, hk⟩ : ∃ k, ct.scBindingScCode = k + 1 := by
    cases h : ct.scBindingScCode with
    | zero => rw [h] at hDR; cases hDR
    | succ k => exact ⟨k, rfl⟩
  rw [hk] at hDR
  simp only [Bool.and_eq_true, beq_iff_eq] at hDR
  obtain ⟨⟨hLsc, hFsc⟩, hScM⟩ := hDR
  obtain ⟨sc, hSc⟩ : ∃ sc, st.getSchedContext? ⟨k⟩ = some sc := by
    cases h : st.getSchedContext? ⟨k⟩ with
    | none => rw [h] at hScM; cases hScM
    | some sc => exact ⟨sc, rfl⟩
  rw [hSc] at hScM
  simp only [Bool.and_eq_true, beq_iff_eq] at hScM
  obtain ⟨hBT, hOldM⟩ := hScM
  obtain ⟨hEq, hF1, hF2, hF3, hF4, hF5, rt', hTr', hbr'⟩ :=
    callRendezvous_inPlace_facts st endpointId ep caller r rt rid payload msg core hM hE hH hT hRid
      hTR
  obtain ⟨ct', hTc', hb', hro'⟩ := hF5 ct hCo
  have hR' := hF4 rp hRp0
  generalize hSt' : storeCallRendezvous st endpointId caller r rt.queueNext rid msg core = st'
    at hEq hF1 hF2 hF3 hR' hTc' hTr'
  have hRpO : st.objects[rid.toObjId]? = some (.reply rp) :=
    (SystemState.getReply?_eq_some_iff _ _ _).mp hRp0
  have hScO : st.objects[(SeLe4n.SchedContextId.toObjId ⟨k⟩)]? = some (.schedContext sc) :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
  have hScR : (SeLe4n.SchedContextId.toObjId ⟨k⟩) ≠ rid.toObjId := fun h => by
    rw [h, hRpO] at hScO; cases hScO
  have hSc' : st'.getSchedContext? ⟨k⟩ = some sc :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
      (hF3 _ _ (fun _ h => by cases h) (fun _ h => by cases h) hScR hScO)
  have hB : sc.boundThread = some caller := by
    show SeLe4n.ThreadId.ofOptCode sc.boundThreadCode = some caller
    rw [hBT]; rfl
  have hC' : lookupTcb st' caller = some ct' := by
    unfold lookupTcb; simp only [hCRes, Bool.false_eq_true, ↓reduceIte, hTc']
  have hCaller : ({ rp with callerCode := SeLe4n.ThreadId.optCode (some caller) } : Reply).caller
      ≠ none := by
    show SeLe4n.ThreadId.ofOptCode (SeLe4n.ThreadId.optCode (some caller)) ≠ none
    rw [SeLe4n.ThreadId.ofOptCode_optCode]; exact Option.some_ne_none _
  have hNe : sc.scReply ≠ some rid := by
    revert hOldM
    cases sc.scReply with
    | none => intro _ h; cases h
    | some old =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
      intro h e; exact h.1.1.1 (Option.some.inj e)
  have hOld : ∀ old, sc.scReply = some old →
      (∃ oR, st'.getReply? old = some oR) ∧
      storeLeavesIndexAndTypes st' old.toObjId .reply = true ∧
      st'.objects.findsInPlace old.toObjId = true := by
    intro old hso
    rw [hso] at hOldM
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isSome_iff_exists] at hOldM
    obtain ⟨⟨⟨hOR, hOL⟩, hOF⟩, oR, hoR⟩ := hOldM
    have hON : old.toObjId ≠ rid.toObjId := fun h => hOR (SeLe4n.ReplyId.toObjId_injective _ _ h)
    exact ⟨⟨oR, (SystemState.getReply?_eq_some_iff _ _ _).mpr
        (hF3 _ _ (fun _ h => by cases h) (fun _ h => by cases h) hON
          ((SystemState.getReply?_eq_some_iff _ _ _).mp hoR))⟩,
      hF2 hOL, (hF1 _).trans hOF⟩
  have hDon := donateSchedContext_eq_inPlace st' caller r ⟨k⟩ sc ct' rt' rid _ hSc' hB hC' hro'
    hR' hRpPrev hRpNext hCaller hNe hOld hTr' hRRes (hF2 hLsc) ((hF1 _).trans hFsc) (hF2 hLR)
    ((hF1 _).trans hFR) (hF2 hLC) ((hF1 _).trans hFC) (hF2 hLH)
  have hRT : st.getTcb? r = some rt := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hDonId : callDonationSchedContext? st' caller r = some ⟨k⟩ := by
    rw [callDonationSchedContext?_eq_bindings]
    simp only [lookupTcb, hRRes, hCRes, Bool.false_eq_true, ↓reduceIte, hTr', hTc',
      Option.map_some, hb', hbr']
    show donationOfBindings (some (SchedContextBinding.ofCodes rt.scBindingScCode
      rt.scBindingOwnerCode)) (some (SchedContextBinding.ofCodes ct.scBindingScCode
      ct.scBindingOwnerCode)) = _
    rw [hRB, hk]
    cases ct.scBindingOwnerCode <;> rfl
  have hScId : callerScId st caller = ⟨k⟩ := by
    unfold callerScId; rw [hCo]; dsimp only; rw [hk]; rfl
  have hEp : st.getEndpoint? endpointId = some ep :=
    (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff caller).mpr hCRes)
  obtain ⟨rv, hrv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff r).mpr hRRes)
  have hcv' := SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv
  have hrv' := SeLe4n.ThreadId.toValid?_some_val_eq _ _ hrv
  refine ⟨(wakeThread ((storePopHead st endpointId true r rt.queueNext).updateTcb r
    (callReceiverTcb msg)) r core).2, ?_⟩
  unfold endpointCallCrossCoreDispatchChecked
  rw [if_pos hFlow]
  unfold endpointCallCrossCoreDispatch
  rw [endpointCallWithCapsOnCore_no_caps _ _ _ _ _ _ hReq, hEq]
  simp only [Except.map, hEp, hH, hcv, hrv]
  unfold applyCallDonationOnCore
  rw [applyCallDonation_characterisation, hcv', hrv', hDonId]
  dsimp only
  rw [hDon]
  unfold performCallDonating
  rw [hScId, hSt']

/-- **The in-place donation keeps the chain**: on the states whose checks pass
it is `donateSchedContext`'s state (`donateSchedContext_eq_inPlace`), so it
carries that transition's chain result. -/
theorem donateSchedContextInPlace_preserves_donationChainWellFormed (st : SystemState)
    (client server : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (donor srv : TCB)
    (rid : SeLe4n.ReplyId) (pr : Reply)
    (hSc : st.getSchedContext? scId = some sc) (hB : sc.boundThread = some client)
    (hC : lookupTcb st client = some donor) (hRO : donor.replyObject = some rid)
    (hR : st.getReply? rid = some pr) (hPrev : pr.prev = none) (hNext : pr.next = none)
    (hCaller : pr.caller ≠ none) (hNe : sc.scReply ≠ some rid)
    (hOld : ∀ old, sc.scReply = some old →
      (∃ oR, st.getReply? old = some oR) ∧
      storeLeavesIndexAndTypes st old.toObjId .reply = true ∧
      st.objects.findsInPlace old.toObjId = true)
    (hS : st.getTcb? server = some srv) (hSRes : server.isReserved = false)
    (hLsc : storeLeavesIndexAndTypes st scId.toObjId .schedContext = true)
    (hFsc : st.objects.findsInPlace scId.toObjId = true)
    (hLr : storeLeavesIndexAndTypes st rid.toObjId .reply = true)
    (hFr : st.objects.findsInPlace rid.toObjId = true)
    (hLc : storeLeavesIndexAndTypes st client.toObjId .tcb = true)
    (hFc : st.objects.findsInPlace client.toObjId = true)
    (hLs : storeLeavesIndexAndTypes st server.toObjId .tcb = true)
    (hObjInv : st.objects.invExt) (hChain : donationChainWellFormed st) :
    donationChainWellFormed (donateSchedContextInPlace st client server scId) :=
  donateSchedContext_preserves_donationChainWellFormed st _ client server scId hObjInv hChain
    (donateSchedContext_eq_inPlace st client server scId sc donor srv rid pr hSc hB hC hRO hR
      hPrev hNext hCaller hNe hOld hS hSRes hLsc hFsc hLr hFr hLc hFc hLs)

end SeLe4n.Kernel
