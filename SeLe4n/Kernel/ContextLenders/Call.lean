-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ContextLenders.Stage
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch
import SeLe4n.Kernel.IPC.Operations.CallLendLabel

/-! # The cross-core Call keeps the lenders' flow

WS-SX SX8.  seL4's `sendIPC` for a Call: the rendezvous (`endpointCallOnCore`,
which links the caller on the reply object its server stashed), the capability
transfer, then — where the call links a reply and the lend is admitted — the
context's donation to the passive server (`donateSchedContext`, a frame
pushed with the caller as its lender), the replenishment migration and the
priority walk.  The fault delivery and the syscall's `.call` arm both run it.

The donation reads the chain facts at the state the rendezvous leaves
(`LendersPremises`), as `Stage.lean` describes; the lend admission
(`callLendAdmits`) is read on the state the call starts from, which holds the
caller's binding unchanged (`endpointCallWithCapsOnCore_sameSchedContextBindings`). -/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace chainObjectsKept

/-- A capability transfer writes CNodes and thread records only. -/
theorem receiveTransferCaps {req : Option (Capability × Array SeLe4n.CPtr)}
    {endpointId : Option SeLe4n.ObjId} {target? : Option (TCB × Option CSpaceAddr)}
    {st st' : SystemState} {summary : CapTransferSummary} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.receiveTransferCaps req endpointId target? st = .ok (summary, st')) :
    chainObjectsKept st st' := by
  have key : ∀ x : SeLe4n.ObjId, ∀ o : KernelObject, st'.objects[x]? = some o →
      (∀ cn, o ≠ .cnode cn) → (∀ t, o ≠ .tcb t) → st.objects[x]? = some o := by
    intro x o hx hCn hT
    rcases receiveTransferCaps_object_cases x hInv h with
      (e | ⟨_, cn', -, h2, -⟩ | ⟨_, t', -, h2, -⟩) | ⟨_, -, -, -, cn', h2⟩
    · rw [← e]; exact hx
    · rw [h2] at hx; cases hx; exact absurd rfl (hCn cn')
    · rw [h2] at hx; cases hx; exact absurd rfl (hT t')
    · rw [h2] at hx; cases hx; exact absurd rfl (hCn cn')
  exact ⟨fun x r hx => key x _ hx (fun _ h => by cases h) (fun _ h => by cases h),
    fun x sc hx => key x _ hx (fun _ h => by cases h) (fun _ h => by cases h)⟩

/-- The priority walk writes thread records and the scheduler only. -/
theorem propagatePipChainCrossCore (st : SystemState) (t : SeLe4n.ThreadId) (ec : CoreId)
    (fuel : Nat) (hInv : st.objects.invExt) :
    chainObjectsKept st (PriorityInheritance.propagatePipChainCrossCore st t ec fuel).1 := by
  have key : ∀ x : SeLe4n.ObjId, ∀ o : KernelObject,
      (PriorityInheritance.propagatePipChainCrossCore st t ec fuel).1.objects[x]? = some o →
      (∀ t, o ≠ .tcb t) → st.objects[x]? = some o := by
    intro x o hx hT
    rcases PriorityInheritance.propagatePipChainCrossCore_objects_pointwise fuel st t ec hInv x with
      e | ⟨_, post, -, hPost, -⟩
    · rw [← e]; exact hx
    · rw [hPost] at hx; cases hx; exact absurd rfl (hT post)
  exact ⟨fun x r hx => key x _ hx (fun _ h => by cases h),
    fun x sc hx => key x _ hx (fun _ h => by cases h)⟩

end chainObjectsKept

/-- The replenishment migration moves release links only. -/
theorem LendersStage.migrateSchedContextReplenishment {ctx : LabelingContext} (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore : CoreId) :
    LendersStage ctx st (_root_.SeLe4n.Kernel.migrateSchedContextReplenishment st scId fromCore toCore) :=
  of_viewsAgree (contextStackViewsAgree_of_objectsAgreeOffReleaseLinks
    (migrateSchedContextReplenishment_agree st scId fromCore toCore))

/-- **The admission's flow, read off the caller's binding**: where the
admission passes, the caller's label flows to the context it holds. -/
theorem callLendAdmits_flows_of_binding {ctx : LabelingContext} {st : SystemState}
    {caller : SeLe4n.ThreadId} {t : TCB} {s : SeLe4n.SchedContextId}
    (hAdm : callLendAdmits ctx st caller = true) (hT : lookupTcb st caller = some t)
    (hS : t.schedContextBinding.scId? = some s) :
    securityFlowsTo (ctx.threadLabelOf caller) (ctx.objectLabelOf s.toObjId) = true := by
  unfold callLendAdmits at hAdm
  rw [hT] at hAdm
  simp only [hS] at hAdm
  exact hAdm

/-- **The call donation carries the lenders' flow** where the caller flows to
every context it holds: the one lend is `donateSchedContext`'s push. -/
theorem applyCallDonation_preserves_contextLendersFlow {ctx : LabelingContext}
    {st st' : SystemState} {callerV receiverV : SeLe4n.ValidThreadId}
    (hP : LendersPremises st) (hInv : contextLendersFlow ctx st)
    (hFlow : ∀ (t : TCB) (s : SeLe4n.SchedContextId), lookupTcb st callerV.val = some t →
      t.schedContextBinding.scId? = some s →
      securityFlowsTo (ctx.threadLabelOf callerV.val) (ctx.objectLabelOf s.toObjId) = true)
    (h : _root_.SeLe4n.Kernel.applyCallDonation st callerV receiverV = .ok st') :
    contextLendersFlow ctx st' := by
  unfold _root_.SeLe4n.Kernel.applyCallDonation at h
  dsimp only at h
  split at h
  · cases h; exact hInv
  · split at h
    · split at h
      · cases h; exact hInv
      · rename_i callerTcb hC
        split at h
        · rename_i s hS
          split at h
          · cases h
          · rename_i st1 hD
            cases h
            exact donateSchedContext_preserves_contextLendersFlow hP.invExt hP.chain hP.linkage
              hInv (hFlow callerTcb s hC hS) hD
        · cases h; exact hInv
    all_goals (cases h; exact hInv)

/-- And its cross-core form: the donation, then the replenishment migration. -/
theorem applyCallDonationOnCore_preserves_contextLendersFlow {ctx : LabelingContext}
    {st st' : SystemState} {callerV receiverV : SeLe4n.ValidThreadId} {donorHome doneeHome : CoreId}
    (hP : LendersPremises st) (hInv : contextLendersFlow ctx st)
    (hFlow : ∀ (t : TCB) (s : SeLe4n.SchedContextId), lookupTcb st callerV.val = some t →
      t.schedContextBinding.scId? = some s →
      securityFlowsTo (ctx.threadLabelOf callerV.val) (ctx.objectLabelOf s.toObjId) = true)
    (h : _root_.SeLe4n.Kernel.applyCallDonationOnCore st callerV receiverV donorHome doneeHome
      = .ok st') :
    contextLendersFlow ctx st' := by
  obtain ⟨st1, hDon, hArm⟩ := applyCallDonationOnCore_ok_decompose _ _ _ _ _ _ h
  have h1 := applyCallDonation_preserves_contextLendersFlow hP hInv hFlow hDon
  rcases hArm with ⟨_, rfl⟩ | ⟨scId, _, rfl⟩
  · exact h1
  · exact LendersStage.migrateSchedContextReplenishment _ _ _ _ h1

/-- **The rendezvous and the capability transfer carry the lenders' flow**:
the rendezvous's one caller link is on a free reply
(`endpointCallOnCore_preserves_contextLendersFlow`), and the transfer writes
CNodes and thread records. -/
theorem endpointCallWithCapsOnCore_preserves_contextLendersFlow {ctx : LabelingContext}
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (core : CoreId) (st : SystemState) (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st) (hFlow : contextLendersFlow ctx st) :
    contextLendersFlow ctx (endpointCallWithCapsOnCore endpointId caller payload core st).1 := by
  have h1 := endpointCallOnCore_preserves_contextLendersFlow (endpointId := endpointId)
    (caller := caller) (payload := payload) (core := core) hInv hChain hFlow
  have hI1 := endpointCallOnCore_preserves_objects_invExt endpointId caller payload core st hInv
  unfold endpointCallWithCapsOnCore
  cases hC : endpointCallOnCore endpointId caller payload core st with
  | mk st1 r =>
    rw [hC] at h1 hI1
    cases r with
    | error e => exact h1
    | ok sgi =>
      dsimp only
      split
      · exact h1
      · split
        · split
          · exact h1
          · rename_i hT
            exact LendersStage.of_kept (chainObjectsKept.receiveTransferCaps hI1 hT) h1
        · exact h1

/-- **The full cross-core Call carries the lenders' flow**: the rendezvous and
the transfer, then the donation where the call links a reply and the lend is
admitted (`lend`; where it passes, the caller's label flows to the context it
holds at the state the call starts from, so to the one it lends), then the
replenishment migration and the priority walk. -/
theorem endpointCallCrossCoreDispatch_preserves_contextLendersFlow {ctx : LabelingContext}
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (executingCore : CoreId) (st : SystemState) (lend : Bool)
    (hInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (hMid : LendersPremises (endpointCallWithCapsOnCore endpointId caller payload executingCore st).1)
    (hAdm : lend = true → callLendAdmits ctx st caller = true)
    (hFlow : contextLendersFlow ctx st) :
    contextLendersFlow ctx (endpointCallCrossCoreDispatch endpointId caller payload executingCore st
      lend).1 := by
  have h1 := endpointCallWithCapsOnCore_preserves_contextLendersFlow endpointId caller payload
    executingCore st hInv hChain hFlow
  have hFrame := endpointCallWithCapsOnCore_sameSchedContextBindings endpointId caller payload
    executingCore st hInv
  unfold endpointCallCrossCoreDispatch
  cases hWc : endpointCallWithCapsOnCore endpointId caller payload executingCore st with
  | mk st' res =>
    rw [hWc] at h1 hFrame hMid
    simp only at h1 hFrame hMid
    cases res with
    | error e => exact h1
    | ok pair =>
      obtain ⟨summary, sgi⟩ := pair
      simp only []
      split
      · split
        · split
          · rename_i callerV receiverV hCV _
            split
            · exact h1
            · rename_i st'' hDon
              rcases applyCallDonationOnCoreWhen_cases hDon with ⟨hL, hDon⟩ | ⟨_, rfl⟩
              · have h2 := applyCallDonationOnCore_preserves_contextLendersFlow hMid h1
                  (fun t s hT hS => by
                    obtain ⟨t0, hT0, hB⟩ := hFrame callerV.val t (lookupTcb_some_objects st' _ t hT)
                    have hT0' : lookupTcb st callerV.val = some t0 :=
                      lookupTcb_of_objects_of_not_reserved st callerV.val t0 hT0
                        (lookupTcb_some_not_reserved st' callerV.val t hT)
                    have hEq : callerV.val = caller := SeLe4n.ThreadId.toValid?_some_val_eq caller callerV hCV
                    rw [hEq] at hT0' ⊢
                    exact callLendAdmits_flows_of_binding (hAdm hL) hT0' (by rw [hB]; exact hS)) hDon
                have hI2 := applyCallDonationOnCore_preserves_objects_invExt _ _ _ _ _ _
                  hMid.invExt hDon
                exact LendersStage.of_kept (chainObjectsKept.propagatePipChainCrossCore _ _ _ _ hI2) h2
              · exact LendersStage.of_kept
                  (chainObjectsKept.propagatePipChainCrossCore _ _ _ _ hMid.invExt) h1
          all_goals exact h1
        · exact h1
      · exact h1

/-- **The flow-checked Call** (the syscall's `.call` arm): a refused gate
returns the state, and a passed one runs the Call under the admission read on
the state it starts from. -/
theorem endpointCallCrossCoreDispatchChecked_preserves_contextLendersFlow {ctx : LabelingContext}
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (executingCore : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (hMid : LendersPremises (endpointCallWithCapsOnCore endpointId caller payload executingCore st).1)
    (hFlow : contextLendersFlow ctx st) :
    contextLendersFlow ctx (endpointCallCrossCoreDispatchChecked ctx endpointId caller payload
      executingCore st).1 := by
  unfold endpointCallCrossCoreDispatchChecked
  split
  · exact endpointCallCrossCoreDispatch_preserves_contextLendersFlow endpointId caller payload
      executingCore st _ hInv hChain hMid id hFlow
  · exact hFlow

end SeLe4n.Kernel
