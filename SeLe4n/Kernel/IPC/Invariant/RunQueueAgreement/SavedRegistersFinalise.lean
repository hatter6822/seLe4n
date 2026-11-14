/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.SavedRegistersFrame
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.SyscallReadiness
import SeLe4n.Kernel.IPC.Invariant.CancelAllReachability

/-!
# The saved-register census over the final delete and revoke

WS-ZA ZA6.24.  The capability-only dispatch's `.cspaceDelete` and
`.cspaceRevoke` arms (`cspaceDeleteSlotZombie`, `cspaceRevokeCdtFinalising`) are
chains of finalising deletes and finalisations.  Their census
(`savedRegsKeptOffCore`) is read off what each step writes.

* **The writers.**  A finalisation writes saved registers in two ways: the
  cancellations restore a thread blocked in IPC to ready with the cancellation
  frame (an endpoint waiter's and a blocked thread's `cancelledEndpointWaiterTcb`,
  a notification waiter's and a reply caller's `restoreToReadyCancelled`), and a
  context's finalisation completes the yield it records (`completeYieldFrom`).
  Every other step of the closed set (`finaliseFinalObject_closed`) writes no
  saved register (`savedRegsKeptExcept`).
* **Their free-ness.**  A thread a cancellation writes is blocked in IPC when it
  is written, and the entry blocks no thread before it (`readyKeptStage`), so it
  was blocked when the entry began: current nowhere (`blockedCurrentNowhere`)
  and resident nowhere (`blockedNotResident`); a thread with no TCB then counts
  as ready, which the readiness frame keeps, so no TCB appears blocked at a
  resident's id.  The yielder a completion names is linked, and no step of the
  entry sets a link (`YieldToCodesUnset`), so it was linked when the entry began
  and no core held it (`yieldLinkedNotResident`).
* **The core release.**  The retire after a finalisation removes only a thread
  no core holds (`threadHeldOnSomeCore`), and nothing after makes a thread held
  on another core, so the census owes a deleted thread nothing.

The step frames compose into the census through the coverage relation the
deletes already carry (`coversWithDeleteBundle`).  The whole capability-only
dispatch's census (ZA6.25, `dispatchCapabilityOnly_savedRegsKeptOffCore`) reads
the final delete and revoke from here
(`cspaceDeleteSlotZombie_savedRegsKeptOffCore`,
`cspaceRevokeCdtFinalising_savedRegsKeptOffCore`).
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-! ### Which threads a step writes -/

namespace savedRegsKeptExcept

variable {W : SeLe4n.ThreadId → Prop}

theorem refl (st : SystemState) : savedRegsKeptExcept W st st := fun _ _ => rfl

theorem trans {a b c : SystemState} (h₁ : savedRegsKeptExcept W a b)
    (h₂ : savedRegsKeptExcept W b c) : savedRegsKeptExcept W a c :=
  fun t ht => (h₂ t ht).trans (h₁ t ht)

theorem mono {W' : SeLe4n.ThreadId → Prop} {pre post : SystemState} (hW : ∀ t, W t → W' t)
    (h : savedRegsKeptExcept W pre post) : savedRegsKeptExcept W' pre post :=
  fun t ht => h t fun hw => ht (hW t hw)

theorem of_eq {pre post : SystemState} (h : ∀ t, post.savedRegs t = pre.savedRegs t) :
    savedRegsKeptExcept W pre post := fun t _ => h t

theorem of_state_eq {pre post : SystemState} (h : post = pre) : savedRegsKeptExcept W pre post := by
  subst h; exact refl _

theorem of_objects_eq {pre post : SystemState} (h : post.objects = pre.objects) :
    savedRegsKeptExcept W pre post := fun t _ => by
  unfold SystemState.savedRegs SystemState.getTcb?; rw [h]

/-- A step that writes run-queue links alone. -/
theorem of_runLinks {pre post : SystemState} (h : post.objectsAgreeOffRunLinks pre) :
    savedRegsKeptExcept W pre post := fun t _ =>
  TCB.map_proj_eq_of_map_withoutRunLinks_eq TCB.registerContext (h.getTcb? t)

/-- A step that writes reply-waiter links alone. -/
theorem of_replyLinks {pre post : SystemState} (h : SystemState.objectsAgreeOffReplyLinks post pre) :
    savedRegsKeptExcept W pre post := fun t _ => h.getTcb?_map TCB.registerContext (fun _ => rfl) t

/-- A thread's TCB rewritten without its saved registers. -/
theorem updateTcb (st : SystemState) (w : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt) (hf : ∀ x, (f x).registerContext = x.registerContext) :
    savedRegsKeptExcept W st (st.updateTcb w f) := fun t _ => by
  by_cases e : t = w
  · subst e
    unfold SystemState.savedRegs
    rw [SystemState.updateTcb_getTcb?_self st t f hInv]
    cases st.getTcb? t with
    | none => rfl
    | some x => exact congrArg some (hf x)
  · exact savedRegs_updateTcb_ne hInv e

/-- A thread of `W` rewritten. -/
theorem updateTcb_written (st : SystemState) (w : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt) (hW : W w) : savedRegsKeptExcept W st (st.updateTcb w f) :=
  fun _ ht => savedRegs_updateTcb_ne hInv fun e => ht (e ▸ hW)

/-- A context rewritten in its slot. -/
theorem updateSchedContext (st : SystemState) (s : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hInv : st.objects.invExt) :
    savedRegsKeptExcept W st (st.updateSchedContext s f) := fun t _ => by
  unfold SystemState.savedRegs; rw [SystemState.updateSchedContext_getTcb? st s f hInv]

/-- **Slot by slot**: every slot keeps its object or holds no TCB on either
side. -/
theorem of_slots {pre post : SystemState}
    (h : ∀ k : SeLe4n.ObjId, post.objects[k]? = pre.objects[k]? ∨
      ((∀ x : TCB, pre.objects[k]? ≠ some (.tcb x)) ∧ ∀ x : TCB, post.objects[k]? ≠ some (.tcb x))) :
    savedRegsKeptExcept W pre post := fun t _ => by
  have a : ∀ st : SystemState, (∀ x : TCB, st.objects[t.toObjId]? ≠ some (.tcb x)) →
      st.getTcb? t = none := fun st h0 => by
    cases e : st.getTcb? t with
    | none => rfl
    | some x => exact absurd ((SystemState.getTcb?_eq_some_iff _ _ _).mp e) (h0 x)
  unfold SystemState.savedRegs
  rcases h t.toObjId with e | ⟨h1, h2⟩
  · unfold SystemState.getTcb?; rw [e]
  · rw [a _ h1, a _ h2]

/-- An object rewritten in its slot by an update that keeps a thread's saved
registers and makes no other object a thread. -/
theorem modifyObject (st : SystemState) (k : SeLe4n.ObjId) (f : KernelObject → KernelObject)
    (hInv : st.objects.invExt)
    (hT : ∀ x : TCB, ∃ y : TCB, f (.tcb x) = .tcb y ∧ y.registerContext = x.registerContext)
    (hO : ∀ o, (∀ x : TCB, o ≠ .tcb x) → ∀ x : TCB, f o ≠ .tcb x) :
    savedRegsKeptExcept W st (st.modifyObject k f) := fun t _ => by
  have hG := modifyObject_objects_getElem (f := f) hInv (st := st) (k := k) t.toObjId
  have a : ∀ s : SystemState, (∀ x : TCB, s.objects[t.toObjId]? ≠ some (.tcb x)) →
      s.getTcb? t = none := fun s h0 => by
    cases e : s.getTcb? t with
    | none => rfl
    | some x => exact absurd ((SystemState.getTcb?_eq_some_iff _ _ _).mp e) (h0 x)
  unfold SystemState.savedRegs
  by_cases hk : k = t.toObjId
  · subst hk
    rw [if_pos rfl] at hG
    cases ho : st.objects[t.toObjId]? with
    | none =>
      rw [ho, Option.map_none] at hG
      rw [a st (fun x hx => by rw [ho] at hx; cases hx),
        a _ (fun x hx => by rw [hG] at hx; cases hx)]
    | some o =>
      rw [ho, Option.map_some] at hG
      by_cases hx : ∃ x : TCB, o = .tcb x
      · obtain ⟨x, rfl⟩ := hx
        obtain ⟨y, hy, hr⟩ := hT x
        rw [hy] at hG
        rw [(SystemState.getTcb?_eq_some_iff st t x).mpr ho,
          (SystemState.getTcb?_eq_some_iff _ t y).mpr hG]
        exact congrArg some hr
      · have hN : ∀ x : TCB, o ≠ .tcb x := fun x e => hx ⟨x, e⟩
        rw [a st (fun x e => hN x (Option.some.inj (ho.symm.trans e))),
          a _ (fun x e => hO o hN x (Option.some.inj (hG.symm.trans e)))]
  · unfold SystemState.getTcb?; rw [hG, if_neg hk]

end savedRegsKeptExcept

/-! ### Writes to free threads give the census -/

/-- WS-ZA ZA6.24: **the step writes the saved registers only of threads no core
other than `e` held at `base`**, an earlier state of the same entry. -/
def savedRegsWrittenFree (e : CoreId) (base pre post : SystemState) : Prop :=
  ∀ t, post.savedRegs t = pre.savedRegs t ∨ offCoreFree e base t

namespace savedRegsWrittenFree

variable {e : CoreId} {base : SystemState}

theorem refl (st : SystemState) : savedRegsWrittenFree e base st st := fun _ => .inl rfl

theorem trans {a b c : SystemState} (h₁ : savedRegsWrittenFree e base a b)
    (h₂ : savedRegsWrittenFree e base b c) : savedRegsWrittenFree e base a c := fun t => by
  rcases h₂ t with x | x
  · rcases h₁ t with y | y
    · exact .inl (x.trans y)
    · exact .inr y
  · exact .inr x

/-- A step writing only threads of `W`, each free at `base`. -/
theorem of_kept {W : SeLe4n.ThreadId → Prop} {pre post : SystemState}
    (h : savedRegsKeptExcept W pre post) (hW : ∀ t, W t → offCoreFree e base t) :
    savedRegsWrittenFree e base pre post := fun t => by
  by_cases hw : W t
  · exact .inr (hW t hw)
  · exact .inl (h t hw)

/-- **The census**: a thread another core holds after the step was held there
at `base`, so it is no thread the step wrote. -/
theorem census {pre post : SystemState} (h : savedRegsWrittenFree e base pre post)
    (hK : currentKeptOffCore e base post) (hR : residentKeptOffCore e base post) :
    savedRegsKeptOffCore e pre post := fun d hd t ht => by
  rcases h t with x | hF
  · exact x
  · exfalso
    rcases ht with h' | h'
    · exact (hF d hd).1 (hK d hd t h')
    · exact (hF d hd).2 (hR d hd t h')

end savedRegsWrittenFree

/-! ### Free-ness at the entry's start -/

/-- WS-ZA ZA6.24: **what the census of a final delete reads at the entry's
start**: the store and the run queues well formed, a blocked thread current
nowhere and resident nowhere, the yield links in agreement and no core holding
a linked thread. -/
structure FinaliseCensusBase (st : SystemState) : Prop where
  objInv : st.objects.invExt
  refined : st.runQueueRefined
  blocked : blockedCurrentNowhere st
  blockedNotResident : st.blockedNotResident
  yieldAgree : st.yieldLinksAgree
  yieldNotResident : st.yieldLinkedNotResident

/-- **A thread blocked now, after steps that block no thread, was blocked at the
entry's start**, so no core held it then.  A thread with no TCB at the start
counts as ready, which the steps keep, so it is no thread blocked now. -/
theorem offCoreFree_of_blockedSince {e : CoreId} {st s : SystemState}
    (B : FinaliseCensusBase st) (hR : readyKeptStage (fun _ => False) st s)
    {t : SeLe4n.ThreadId} {tcb : TCB} (hT : s.getTcb? t = some tcb) (hS : tcb.ipcState ≠ .ready) :
    offCoreFree e st t := by
  have hNR : ¬ st.readyOrAbsent t := fun h => hS (hR B.objInv B.refined t id h tcb hT)
  cases hx : st.getTcb? t with
  | none => exact absurd (fun x h => by rw [hx] at h; cases h) hNR
  | some x =>
    exact offCoreFree_of_blocked B.blocked B.blockedNotResident hx
      (fun h => hNR fun y hy => by rw [hx] at hy; cases hy; exact h)

/-- **The yielder a context records now was linked at the entry's start**, so
no core held it then: on the entry's states the links agree, and no step of the
entry sets a yield-to code. -/
theorem offCoreFree_of_yieldFromSince {e : CoreId} {st s : SystemState}
    (B : FinaliseCensusBase st) (hE : SystemState.RunQueueEntryStage st s)
    {c : SeLe4n.SchedContextId} {sc : SchedContext} {k : Nat}
    (hS : s.getSchedContext? c = some sc) (hC : sc.yieldFromCode = k + 1) :
    offCoreFree e st ⟨k⟩ :=
  offCoreFree_of_yieldCode B.yieldNotResident
    (yieldCode_of_unset (hE.1.live B.objInv B.refined).unset
      (yieldCode_of_yieldFrom (hE.1.yield B.objInv B.refined B.yieldAgree) hS hC))

/-! ### The finalisation's register-free writes -/

namespace savedRegsKeptExcept

variable {W : SeLe4n.ThreadId → Prop}

/-- An endpoint rewritten in its slot. -/
theorem modifyEndpoint (st : SystemState) (k : SeLe4n.ObjId) (f : KernelObject → KernelObject)
    (hInv : st.objects.invExt) (hE : ∀ ep, ∃ ep', f (.endpoint ep) = .endpoint ep')
    (hO : ∀ o, (∀ ep, o ≠ .endpoint ep) → f o = o) :
    savedRegsKeptExcept W st (st.modifyObject k f) :=
  modifyObject st k f hInv (fun x => ⟨x, hO _ (fun _ h => by cases h), rfl⟩) (fun o ho x hx => by
    by_cases he : ∃ ep, o = .endpoint ep
    · obtain ⟨ep, rfl⟩ := he
      obtain ⟨ep', h'⟩ := hE ep
      rw [h'] at hx; cases hx
    · rw [hO o (fun ep h => he ⟨ep, h⟩)] at hx; exact ho x hx)

/-- A notification rewritten in its slot. -/
theorem modifyNotification (st : SystemState) (k : SeLe4n.ObjId) (g : Notification → Notification)
    (hInv : st.objects.invExt) :
    savedRegsKeptExcept W st (st.modifyObject k (mapNotificationObject g)) :=
  modifyObject st k _ hInv (fun x => ⟨x, rfl, rfl⟩) (fun o ho x hx => by
    cases o with
    | notification n => cases hx
    | tcb y => exact ho y rfl
    | _ => cases hx)

end savedRegsKeptExcept

/-- **A wake writes no saved register**: the woken thread's IPC state and
run-queue links, and the other threads' run-queue links. -/
theorem savedRegs_enqueueRunnableOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    (enqueueRunnableOnCore st c tid).savedRegs t = st.savedRegs t := by
  unfold SystemState.savedRegs
  by_cases h : t = tid
  · subst h
    cases hT : st.getTcb? t with
    | none => rw [enqueueRunnableOnCore_getTcb?_eq_none st c t t hInv hT]
    | some x =>
      obtain ⟨y, hy, hr⟩ := enqueueRunnableOnCore_getTcb?_regContext st c t t x hInv hT
      rw [hy]; exact congrArg some hr
  · exact TCB.map_proj_eq_of_map_withoutRunLinks_eq TCB.registerContext
      (enqueueRunnableOnCore_getTcb?_ne st c tid t hInv h)

/-- The in-place pop of an endpoint queue's head writes queue links alone. -/
theorem storePopHead_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop} (st : SystemState)
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (head : SeLe4n.ThreadId)
    (next : Option SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    savedRegsKeptExcept W st (storePopHead st endpointId isReceiveQ head next) ∧
      (storePopHead st endpointId isReceiveQ head next).objects.invExt := by
  unfold storePopHead
  have k1 := savedRegsKeptExcept.modifyEndpoint (W := W) st endpointId
    (popEndpoint isReceiveQ (SeLe4n.ThreadId.optCode next)) hInv
    (fun ep => by simp only [popEndpoint]; split <;> exact ⟨_, rfl⟩)
    (fun o ho => by cases o <;> first | rfl | exact absurd rfl (ho _))
  have i1 := modifyObject_preserves_objects_invExt
    (f := popEndpoint isReceiveQ (SeLe4n.ThreadId.optCode next)) (k := endpointId) hInv
  generalize st.modifyObject endpointId (popEndpoint isReceiveQ (SeLe4n.ThreadId.optCode next)) = s1
    at k1 i1
  have k2 : savedRegsKeptExcept W s1 (match next with | none => s1 | some n => s1.updateTcb n tcbAsQueueHead) ∧
      (match next with | none => s1 | some n => s1.updateTcb n tcbAsQueueHead).objects.invExt := by
    cases next with
    | none => exact ⟨.refl _, i1⟩
    | some n => exact ⟨.updateTcb s1 n _ i1 (fun _ => rfl), SystemState.updateTcb_preserves_objects_invExt _ _ _ i1⟩
  exact ⟨(k1.trans k2.1).trans (.updateTcb _ head _ k2.2 (fun _ => rfl)),
    SystemState.updateTcb_preserves_objects_invExt _ _ _ k2.2⟩

/-- **An endpoint waiter's cancel writes the waiter alone**: the pop writes queue
links; a waiter with no fault is set to restart and woken, the wake writing
none, and a faulted waiter is left `Inactive` with its registers kept. -/
theorem storeEndpointWaiterCancelled_savedRegsKeptExcept (st : SystemState)
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (t : SeLe4n.ThreadId)
    (next : Option SeLe4n.ThreadId) (faulted : Bool) (hInv : st.objects.invExt) :
    savedRegsKeptExcept (· = t) st
      (storeEndpointWaiterCancelled st endpointId isReceiveQ t next faulted) := by
  obtain ⟨k1, i1⟩ := storePopHead_savedRegsKeptExcept (W := (· = t)) st endpointId isReceiveQ t next hInv
  unfold storeEndpointWaiterCancelled
  split
  · unfold storeEndpointWaiterFaulted
    exact k1.trans (.updateTcb _ t _ i1 (fun x => faultedEndpointWaiterTcb_registerContext x))
  · unfold storeEndpointWaiterRestarted wakeCancelledWaiter
    have i2 := SystemState.updateTcb_preserves_objects_invExt _ t cancelledEndpointWaiterTcb i1
    exact (k1.trans (.updateTcb_written _ t _ i1 rfl)).trans
      (.of_eq (savedRegs_enqueueRunnableOnCore _ _ t i2))

/-- The in-place removal of a thread from an endpoint queue writes queue links
alone. -/
theorem storeQueueRemove_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop} (st : SystemState)
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (ep : Endpoint)
    (tcb : TCB) (hInv : st.objects.invExt) :
    savedRegsKeptExcept W st (storeQueueRemove st endpointId isReceiveQ tid ep tcb) ∧
      (storeQueueRemove st endpointId isReceiveQ tid ep tcb).objects.invExt := by
  have hEp : ∀ (s : SystemState) (f : KernelObject → KernelObject), s.objects.invExt →
      (∀ ep, ∃ ep', f (.endpoint ep) = .endpoint ep') → (∀ o, (∀ ep, o ≠ .endpoint ep) → f o = o) →
      savedRegsKeptExcept W s (s.modifyObject endpointId f) ∧
        (s.modifyObject endpointId f).objects.invExt := fun s f hI hE hO =>
    ⟨.modifyEndpoint s endpointId f hI hE hO, modifyObject_preserves_objects_invExt hI⟩
  have hTcb : ∀ (s : SystemState) (w : SeLe4n.ThreadId) (f : TCB → TCB), s.objects.invExt →
      (∀ x, (f x).registerContext = x.registerContext) →
      savedRegsKeptExcept W s (s.updateTcb w f) ∧ (s.updateTcb w f).objects.invExt :=
    fun s w f hI hf => ⟨.updateTcb s w f hI hf, SystemState.updateTcb_preserves_objects_invExt _ _ _ hI⟩
  have hHead : ∀ s : SystemState, s.objects.invExt →
      savedRegsKeptExcept W s (s.modifyObject endpointId
        (headAdvancedEndpoint isReceiveQ tcb.queueNextCode)) ∧
      (s.modifyObject endpointId (headAdvancedEndpoint isReceiveQ tcb.queueNextCode)).objects.invExt :=
    fun s hI => hEp s _ hI (fun ep => by simp only [headAdvancedEndpoint]; exact ⟨_, rfl⟩)
      (fun o ho => by cases o <;> first | rfl | exact absurd rfl (ho _))
  have hEnds : ∀ s : SystemState, s.objects.invExt →
      savedRegsKeptExcept W s (s.modifyObject endpointId (endsSetEndpoint isReceiveQ
        (removedEndCode (ep.headCodeOf isReceiveQ) (tid.val + 1) tcb.queueNextCode)
        (removedEndCode (ep.tailCodeOf isReceiveQ) (tid.val + 1) tcb.queuePrevCode))) ∧
      (s.modifyObject endpointId (endsSetEndpoint isReceiveQ
        (removedEndCode (ep.headCodeOf isReceiveQ) (tid.val + 1) tcb.queueNextCode)
        (removedEndCode (ep.tailCodeOf isReceiveQ) (tid.val + 1) tcb.queuePrevCode))).objects.invExt :=
    fun s hI => hEp s _ hI (fun ep => by simp only [endsSetEndpoint]; exact ⟨_, rfl⟩)
      (fun o ho => by cases o <;> first | rfl | exact absurd rfl (ho _))
  have hFin : ∀ s : SystemState, savedRegsKeptExcept W st s → s.objects.invExt →
      savedRegsKeptExcept W st ((s.modifyObject endpointId (endsSetEndpoint isReceiveQ
        (removedEndCode (ep.headCodeOf isReceiveQ) (tid.val + 1) tcb.queueNextCode)
        (removedEndCode (ep.tailCodeOf isReceiveQ) (tid.val + 1) tcb.queuePrevCode))).updateTcb
          tid tcbOffQueue) ∧
      ((s.modifyObject endpointId (endsSetEndpoint isReceiveQ
        (removedEndCode (ep.headCodeOf isReceiveQ) (tid.val + 1) tcb.queueNextCode)
        (removedEndCode (ep.tailCodeOf isReceiveQ) (tid.val + 1) tcb.queuePrevCode))).updateTcb
          tid tcbOffQueue).objects.invExt := fun s k hI =>
    let E := hEnds s hI
    let T := hTcb _ tid tcbOffQueue E.2 (fun _ => rfl)
    ⟨(k.trans E.1).trans T.1, T.2⟩
  have hNext : ∀ s : SystemState, savedRegsKeptExcept W st s → s.objects.invExt →
      savedRegsKeptExcept W st (match tcb.queueNext with
        | some n => s.updateTcb n (queueUnlinkSuccessor tcb) | none => s) ∧
      (match tcb.queueNext with
        | some n => s.updateTcb n (queueUnlinkSuccessor tcb) | none => s).objects.invExt :=
    fun s k hI => by
      cases tcb.queueNext with
      | some n =>
        obtain ⟨k1, i1⟩ := hTcb s n (queueUnlinkSuccessor tcb) hI (fun _ => rfl)
        exact ⟨k.trans k1, i1⟩
      | none => exact ⟨k, hI⟩
  unfold storeQueueRemove
  dsimp only
  cases hP : tcb.queuePPrev with
  | none =>
    obtain ⟨k2, i2⟩ := hNext st (.refl _) hInv
    exact hFin _ k2 i2
  | some pp =>
    cases pp with
    | endpointHead =>
      obtain ⟨k1, i1⟩ := hHead st hInv
      obtain ⟨k2, i2⟩ := hNext _ k1 i1
      exact hFin _ k2 i2
    | tcbNext p =>
      obtain ⟨k1, i1⟩ := hTcb st p (queueUnlinkPredecessor tcb) hInv (fun _ => rfl)
      obtain ⟨k2, i2⟩ := hNext _ k1 i1
      exact hFin _ k2 i2

/-- **A blocked thread's endpoint cancel writes the thread alone**: the removal
writes queue links, and the thread's rewrite sets it to restart. -/
theorem storeEndpointBlockedCancelled_savedRegsKeptExcept (st : SystemState)
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (t : SeLe4n.ThreadId) (ep : Endpoint)
    (tcb : TCB) (hInv : st.objects.invExt) :
    savedRegsKeptExcept (· = t) st (storeEndpointBlockedCancelled st endpointId isReceiveQ t ep tcb) := by
  unfold storeEndpointBlockedCancelled
  obtain ⟨k1, i1⟩ := storeQueueRemove_savedRegsKeptExcept (W := (· = t)) st endpointId isReceiveQ t
    ep tcb hInv
  exact k1.trans (.updateTcb_written _ t _ i1 rfl)

/-- The notification unbind writes a thread's binding code and a notification. -/
theorem storeUnbindNotification_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop}
    (st : SystemState) (t : SeLe4n.ThreadId) (n : SeLe4n.ObjId) (hInv : st.objects.invExt) :
    savedRegsKeptExcept W st (storeUnbindNotification st t n) := by
  unfold storeUnbindNotification
  exact (savedRegsKeptExcept.updateTcb st t (fun t => { t with boundNotificationCode := 0 }) hInv
    (fun _ => rfl)).trans
    (.modifyNotification _ n _ (SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv))

/-- A finalised thread's suspend: the deschedule writes run-queue links, the
mark the thread's state and message. -/
theorem finaliseSuspend_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop} (st : SystemState)
    (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    savedRegsKeptExcept W st ((descheduleAtPlacement st t).updateTcb t finalisedSuspendMark) :=
  (savedRegsKeptExcept.of_runLinks (descheduleAtPlacement_objectsAgreeOffRunLinks st t)).trans
    (.updateTcb _ t _ (descheduleAtPlacement_preserves_objects_invExt st t hInv) (fun _ => rfl))

/-- A thread's yield link cancelled: a context's end and the thread's code. -/
theorem cancelYieldTo_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop} (st : SystemState)
    (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    savedRegsKeptExcept W st (cancelYieldTo st t) := by
  unfold cancelYieldTo
  split
  · split
    · exact .refl _
    · exact (savedRegsKeptExcept.updateSchedContext st _ _ hInv).trans
        (.updateTcb _ t _ (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv)
          (fun _ => rfl))
  · exact .refl _

/-- A context's release of its bound thread writes the context, its release
queue and the thread's binding codes. -/
theorem cancelBoundDonationOnCore_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop}
    {st st' : SystemState} {t : SeLe4n.ThreadId} {tcb : TCB} (hInv : st.objects.invExt)
    (h : cancelBoundDonationOnCore st t tcb = .ok st') : savedRegsKeptExcept W st st' := by
  cases hB : tcb.schedContextBinding with
  | bound scId =>
    obtain ⟨hSelf, hOther⟩ := cancelBoundDonationOnCore_getTcb? st st' t tcb scId hB hInv h
    intro x _
    unfold SystemState.savedRegs
    by_cases hx : x.toObjId = t.toObjId
    · obtain rfl := SeLe4n.ThreadId.toObjId_injective _ _ hx
      rw [hSelf]; cases st.getTcb? x <;> rfl
    · rw [hOther x hx]
  | _ => unfold cancelBoundDonationOnCore at h; rw [hB] at h; cases h

/-! ### The cancellations' register-free pieces -/

namespace savedRegsKeptExcept

variable {W : SeLe4n.ThreadId → Prop}

/-- Every thread's saved registers kept, read through `Option.map`. -/
theorem of_map {pre post : SystemState}
    (h : ∀ x, (post.getTcb? x).map TCB.registerContext = (pre.getTcb? x).map TCB.registerContext) :
    savedRegsKeptExcept W pre post := fun t _ => h t

/-- The endpoint-queue removal writes queue links alone. -/
theorem of_removeFromBlockingEndpoint (st : SystemState) (tid : SeLe4n.ThreadId) (e : SeLe4n.ObjId)
    (hInv : st.objects.invExt) : savedRegsKeptExcept W st (removeFromBlockingEndpoint st tid e) :=
  of_map fun x => by
    rw [removeFromBlockingEndpoint_getTcb?_eq_splice st tid e hInv x]
    exact spliceOutMidQueueNode_tcbField_frame TCB.registerContext (fun _ _ _ _ _ _ => rfl) st tid
      hInv x

/-- The notification-queue removal writes queue links alone. -/
theorem of_removeFromNotificationWaitQueue (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : savedRegsKeptExcept W st (removeFromNotificationWaitQueue st tid) :=
  of_map (removeFromNotificationWaitQueue_tcbField_frame TCB.registerContext
    (fun _ _ _ _ _ _ => rfl) st tid hInv)

/-- The loan's return writes contexts and binding codes alone. -/
theorem of_returnDonationToCancelledCaller (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB)
    (hInv : st.objects.invExt) :
    savedRegsKeptExcept W st (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) :=
  of_map fun x => by
    unfold Lifecycle.Suspend.returnDonationToCancelledCaller
    cases hD : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV with
    | none => rfl
    | some p =>
      obtain ⟨scId, holder⟩ := p
      cases hT : st.getTcb? v with
      | none => rfl
      | some _ =>
        dsimp only
        cases hRet : returnDonatedSchedContextResolved st holder scId v with
        | error _ => rfl
        | ok st' =>
          obtain ⟨newOwner?, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
          exact returnDonatedSchedContext_getTcb?_map_eq TCB.registerContext (fun _ _ _ => rfl) _
            st' holder scId v hInv newOwner? hPop x

/-- The pop off an unheld context, and its settle, rewrite the recipient's
binding codes and no thread's registers; the sever writes no thread. -/
theorem of_finaliseReplyUnheldPop (st : SystemState) (r : Reply) (c : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    savedRegsKeptExcept W st (finaliseReplyUnheldPop st r c) :=
  of_map fun x => by
    rcases finaliseReplyUnheldPop_cases st r c with e | ⟨_, _, st', _, _, hOk, e⟩ |
        ⟨_, _, _, _, _, _, hOk, e⟩ <;> rw [e]
    · rw [SchedContextOps.settleReturnedContext_getTcb?]
      obtain ⟨_, _, ot, -, -, -, -, hO, -, -, hO', tBwd, tFwd, -, -⟩ :=
        returnUnheldSchedContext_objects hInv hOk
      by_cases e : x.toObjId = c.toObjId
      · rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr (e ▸ hO'),
          (SystemState.getTcb?_eq_some_iff _ _ _).mpr (e ▸ hO)]
        rfl
      · cases h1 : st.getTcb? x with
        | some t0 =>
          rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr
            (tFwd _ _ e ((SystemState.getTcb?_eq_some_iff _ _ _).mp h1))]
        | none =>
          cases h2 : st'.getTcb? x with
          | none => rfl
          | some t1 =>
            have := tBwd _ _ e ((SystemState.getTcb?_eq_some_iff _ _ _).mp h2)
            rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr this] at h1
            cases h1
    · rw [severUnheldSchedContext_getTcb?_eq hInv hOk]

/-- The reply-frame cut writes replies and contexts alone. -/
theorem of_cutThreadReplyFrameOut (st : SystemState) (tcb : TCB) (hInv : st.objects.invExt) :
    savedRegsKeptExcept W st (cutThreadReplyFrameOut st tcb) :=
  of_map fun x => by rw [cutThreadReplyFrameOut_getTcb?_eq _ tcb hInv x]

/-- The reply-link teardown clears one TCB field and consumes one reply. -/
theorem of_consumeReplyLink (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt) :
    savedRegsKeptExcept W st (Lifecycle.Suspend.consumeReplyLink st tid tcb) :=
  of_map (consumeReplyLink_map_frame TCB.registerContext (fun _ => rfl) st tid tcb hInv)

/-- The restore writes the restored thread alone. -/
theorem of_restoreToReadyStaging_written (st : SystemState) (tid : SeLe4n.ThreadId)
    (restart : Bool) (hInv : st.objects.invExt) (hW : W tid) :
    savedRegsKeptExcept W st (Lifecycle.Suspend.restoreToReadyStaging st tid restart) := by
  unfold Lifecycle.Suspend.restoreToReadyStaging
  exact updateTcb_written st tid _ hInv hW

/-- The boost's propagation writes boost codes and run-queue links alone. -/
theorem of_propagatePipChainCrossCore (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId)
    (fuel : Nat) (hInv : st.objects.invExt) :
    savedRegsKeptExcept W st (PriorityInheritance.propagatePipChainCrossCore st tid ec fuel).1 :=
  of_map fun x => SystemState.map_tcbField_eq_of_refines TCB.registerContext
    (fun t0 hT0 => by
      obtain ⟨t', hT'⟩ := Option.isSome_iff_exists.mp
        (PriorityInheritance.propagatePipChainCrossCore_getTcb?_isSome fuel st tid ec hInv x
          (by rw [hT0]; rfl))
      obtain ⟨t1, p, h1, hw⟩ := PriorityInheritance.propagatePipChainCrossCore_tcb_backward st tid
        ec fuel hInv x t' ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT')
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr h1] at hT0
      cases hT0
      exact ⟨t', hT', (TCB.proj_eq_of_withoutRunLinks_eq TCB.registerContext hw).trans rfl⟩)
    (fun t' hT' => by
      obtain ⟨t1, _, h1, _⟩ := PriorityInheritance.propagatePipChainCrossCore_tcb_backward st tid
        ec fuel hInv x t' ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT')
      exact ⟨t1, (SystemState.getTcb?_eq_some_iff _ _ _).mpr h1⟩)

end savedRegsKeptExcept

/-- **A cancellation writes the cancelled thread alone**: every arm removes it
from its queue, returns its loan, cuts its reply frame and consumes its
reply link — none a saved register — and restores it, which moves its
saved PC to its restart PC in its own context. -/
theorem cancelIpcBlocking_savedRegsKeptExcept (st : SystemState) (v : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt) :
    savedRegsKeptExcept (· = v) st (Lifecycle.Suspend.cancelIpcBlocking st v tcb) := by
  unfold Lifecycle.Suspend.cancelIpcBlocking Lifecycle.Suspend.restoreToReadyCancelled
  have hQ := fun (s : SystemState) (hs : s.objects.invExt) =>
    savedRegsKeptExcept.of_restoreToReadyStaging_written (W := (· = v)) s v
      true hs rfl
  cases tcb.ipcState with
  | ready => exact .refl _
  | blockedOnSend e =>
    exact (savedRegsKeptExcept.of_removeFromBlockingEndpoint st v e hInv).trans
      (hQ _ (removeFromBlockingEndpoint_preserves_objects_invExt st v e hInv))
  | blockedOnReceive e =>
    exact (savedRegsKeptExcept.of_removeFromBlockingEndpoint st v e hInv).trans
      (hQ _ (removeFromBlockingEndpoint_preserves_objects_invExt st v e hInv))
  | blockedOnCall e =>
    exact (savedRegsKeptExcept.of_removeFromBlockingEndpoint st v e hInv).trans
      (hQ _ (removeFromBlockingEndpoint_preserves_objects_invExt st v e hInv))
  | blockedOnNotification _ =>
    exact (savedRegsKeptExcept.of_removeFromNotificationWaitQueue st v hInv).trans
      (hQ _ (removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv))
  | blockedOnReply _ _ =>
    have hR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt st v tcb hInv
    have hS := cutThreadReplyFrameOut_preserves_objects_invExt _ tcb hR
    have hT := Lifecycle.Suspend.restoreToReadyStaging_invExt _ v true hS
    exact ((((savedRegsKeptExcept.of_returnDonationToCancelledCaller st v tcb hInv).trans
      (savedRegsKeptExcept.of_cutThreadReplyFrameOut _ tcb hR)).trans (hQ _ hS)).trans
      (savedRegsKeptExcept.of_consumeReplyLink _ v tcb hT)).trans
      (savedRegsKeptExcept.of_replyLinks
        (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffReplyLinks _ v _))

/-- **A reply's caller cancel writes the caller alone**: the reclaim's extra
steps write run-queue links and release fields, the boost's revert boost codes. -/
theorem finaliseReplyCancel_savedRegsKeptExcept (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (hInv : st.objects.invExt) :
    savedRegsKeptExcept (· = c) st
      (finaliseReplyRevert (cancelIpcBlockingReclaimed c t st) t.blockingServer?) := by
  have hI1 := cancelIpcBlockingReclaimed_objects_invExt c t st
    (Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt st c t hInv)
  have h1 : savedRegsKeptExcept (· = c) st (cancelIpcBlockingReclaimed c t st) :=
    (cancelIpcBlocking_savedRegsKeptExcept st c t hInv).trans
      (savedRegsKeptExcept.of_map fun x => by
        rw [← TCB.map_proj_eq_of_map_withoutRunLinks_eq TCB.registerContext
          (cancelIpcBlockingReclaimed_getTcb? c t st x)])
  unfold finaliseReplyRevert
  cases t.blockingServer? with
  | none => exact h1
  | some sv => exact h1.trans (.of_propagatePipChainCrossCore _ sv _ _ hI1)

/-! ### The finalisation's other steps -/

namespace savedRegsKeptExcept

variable {W : SeLe4n.ThreadId → Prop}

/-- A reply stored over a reply. -/
theorem storeObject_replyOver {s s1 : SystemState} {rid : SeLe4n.ReplyId} {r r' : Reply}
    (hInv : s.objects.invExt) (hR : s.getReply? rid = some r)
    (hS : storeObject rid.toObjId (.reply r') s = .ok ((), s1)) : savedRegsKeptExcept W s s1 :=
  of_slots fun k => by
    by_cases hk : k = rid.toObjId
    · subst hk
      refine .inr ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [(SystemState.getReply?_eq_some_iff _ _ _).mp hR] at hx; cases hx
      · rw [storeObject_objects_eq' s _ _ _ hInv hS] at hx; cases hx
    · exact .inl (storeObject_objects_ne s s1 _ k _ hk hInv hS)

end savedRegsKeptExcept

/-- A thread blocked on an endpoint queue's side is blocked. -/
theorem blockedOnQueueSide_notReady {q : Bool} {e : SeLe4n.ObjId} {t : TCB}
    (h : blockedOnQueueSide q e t = true) : t.ipcState ≠ .ready := by
  have h' := blockedOnQueueSide_ipcState h
  cases q
  · rcases h'.2 rfl with x | x <;> rw [x] <;> exact fun y => by cases y
  · rw [h'.1 rfl]; exact fun y => by cases y

/-- **An endpoint queue's head is blocked** (`queueHeadBlockedConsistent`). -/
theorem endpointWaiter_notReady {s : SystemState} {e : SeLe4n.ObjId} {ep : Endpoint} {q : Bool}
    {t : SeLe4n.ThreadId} {tcb : TCB} (hQ : queueHeadBlockedConsistent s)
    (hE : s.getEndpoint? e = some ep) (hH : (endpointWaitQueue ep q).head = some t)
    (hT : s.getTcb? t = some tcb) : tcb.ipcState ≠ .ready := by
  have h := hQ e ep t tcb ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE)
    ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT)
  unfold endpointWaitQueue at hH
  cases q
  · simp only [Bool.false_eq_true, ↓reduceIte] at hH
    rcases h.2 hH with x | x <;> rw [x] <;> exact fun y => by cases y
  · simp only [↓reduceIte] at hH
    rw [h.1 hH]; exact fun y => by cases y

/-! ### The finalisation's census -/

section
open SeLe4n.Kernel.Lifecycle.Suspend

/-- WS-ZA ZA6.24: **a finalisation writes the saved registers only of threads no
core other than `e` held at the entry's start**, step by step over the closed set
(`finaliseFinalObject_closed_linked`).  Each step keeps the readiness frame
(`finaliseFinalObject_readyEntry`) and the bundle the delete carries
(`finaliseFinalObject_preserves_finaliseLoanBundle`); a cancellation writes the
thread it cancels, blocked when it is written (an endpoint queue's head by
`queueHeadBlockedConsistent`, the others by their admission), so blocked at the
start (`offCoreFree_of_blockedSince`); a completion writes the yielder its
context records, linked at the start (`offCoreFree_of_yieldFromSince`); every
other step writes no saved register. -/
theorem finaliseFinalObject_savedRegsWrittenFree {e : CoreId} {st s : SystemState}
    (B : FinaliseCensusBase st)
    (hR : SystemState.RunQueueEntryStage st s ∧ readyKeptStage (fun _ => False) st s)
    (hL : finalisingDeleteBundle s) (target : Nat) :
    savedRegsWrittenFree e st s (finaliseFinalObject target s) := by
  let P : SystemState → Prop := fun s' =>
    (SystemState.RunQueueEntryStage st s' ∧ readyKeptStage (fun _ => False) st s') ∧
      finaliseLoanBundle s' ∧ savedRegsWrittenFree e st s s'
  have step : ∀ {a b : SystemState} {W : SeLe4n.ThreadId → Prop}, P a →
      (SystemState.RunQueueEntryStage st b ∧ readyKeptStage (fun _ => False) st b) →
      finaliseLoanBundle b → savedRegsKeptExcept W a b → (∀ t, W t → offCoreFree e st t) → P b :=
    fun h r l k f => ⟨r, l, h.2.2.trans (.of_kept k f)⟩
  have none : ∀ t : SeLe4n.ThreadId, (fun _ => False) t → offCoreFree e st t := fun _ h => h.elim
  have blocked : ∀ {a : SystemState} {t : SeLe4n.ThreadId} {tcb : TCB}, P a → a.getTcb? t = some tcb →
      tcb.ipcState ≠ .ready → ∀ u, u = t → offCoreFree e st u := fun h hT hS u hu => by
    subst hu; exact offCoreFree_of_blockedSince B h.1.2 hT hS
  refine (finaliseFinalObject_closed_linked P ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ target s
    ⟨hR, hL.1, .refl s⟩ hL.1.2.1 hL.2).1.2.2
  · intro en q s ep t tcb h hE hH hT hC
    have R := h.1; have L := h.2.1
    exact step h (storeEndpointWaiterCancelled_readyEntry R hE hH hT hC _)
      (L.of_frame (storeEndpointWaiterCancelled_preserves_ipcInvariantFull s en q ep t tcb L.2.1 L.1
        hE hH hT hC _) (FinaliseFrame.storeEndpointWaiterCancelled s en q t _ _ L.2.1))
      (storeEndpointWaiterCancelled_savedRegsKeptExcept s en q t tcb.queueNext _ L.2.1)
      (blocked h hT (endpointWaiter_notReady L.1.queueHeadBlockedConsistent hE hH hT))
  · intro n s _ t tcb h _ _ hT hC
    have R := h.1; have L := h.2.1
    have F := FinaliseFrame.notificationCancel s t tcb n L.2.1 (notificationWaiterCancellable_blocked hC)
    exact step h (readyEntry_stage R (notificationWaiterCancel_runQueueStage s n t tcb hT hC))
      (L.of_frame (notificationWaiterCancel_preserves_ipcInvariantFull s n t tcb L.2.1 L.1 hT hC)
        (F.trans (FinaliseFrame.wakeCancelledWaiter _ t F.invExt)))
      ((cancelIpcBlocking_savedRegsKeptExcept s t tcb L.2.1).trans
        (.of_eq (savedRegs_enqueueRunnableOnCore _ _ t
          (cancelIpcBlocking_preserves_objects_invExt s t tcb L.2.1))))
      (blocked h hT (by rw [notificationWaiterCancellable_blocked hC]; exact fun y => by cases y))
  · intro n s _ t h _ _ hCode hIn
    have R := h.1; have L := h.2.1
    have hSpec := unbindNotification_of_inPlace s t hIn
    rw [hCode, Nat.add_sub_cancel] at hSpec
    exact step h (readyEntry_stage R (unbindNotification_runQueueStage hSpec))
      (L.of_frame (storeUnbindNotification_preserves_ipcInvariantFull s n t L.2.1 L.1 hCode hIn)
        (FinaliseFrame.storeUnbindNotification s t n L.2.1))
      (storeUnbindNotification_savedRegsKeptExcept s t n L.2.1) none
  · intro s t tcb h hT hS hO hId
    have R := h.1; have L := h.2.1
    exact step h (readyEntry_stage R (descheduleAt_runQueueStage s t _))
      (L.of_frame (finaliseScDescheduleStep_keepsIpcInvariantFull s t tcb ⟨L.1, L.2.1⟩ hT hS hO hId).1
        (FinaliseFrame.descheduleAt s t _ L.2.1))
      (.of_runLinks (descheduleAtPlacement_objectsAgreeOffRunLinks s t)) none
  · intro s s' t tcb sc x h hT hS hSc hB hOk
    have R := h.1; have L := h.2.1
    exact step h (readyEntry_stage R (cancelBoundDonationOnCore_runQueueStage hOk))
      (L.of_frame (finaliseScReleaseStep_keepsIpcInvariantFull s s' t tcb sc x ⟨L.1, L.2.1⟩ hT hS
        hSc hB hOk).1 (FinaliseFrame.cancelBoundDonationOnCore L.2.1 hOk))
      (cancelBoundDonationOnCore_savedRegsKeptExcept L.2.1 hOk) none
  · intro s n t tcb nt h hT hI hN hC
    have R := h.1; have L := h.2.1
    exact step h (readyEntry_stage R (cancelIpcBlocking_runQueueStage s t tcb
        (by unfold Lifecycle.Suspend.cancelledCallerDonation?; rw [hI])))
      (L.of_frame (finaliseNotificationCancelStep_keepsIpcInvariantFull s n t tcb nt ⟨L.1, L.2.1⟩ hT
        hI hN hC).1 (FinaliseFrame.notificationCancel s t tcb n L.2.1 hI))
      (cancelIpcBlocking_savedRegsKeptExcept s t tcb L.2.1)
      (blocked h hT (by rw [hI]; exact fun y => by cases y))
  · intro s en q t ep tcb h hT hE hC
    have R := h.1; have L := h.2.1
    exact step h (readyEntry_stage R (storeEndpointBlockedCancelled_runQueueStage s en q t ep tcb hT hE hC))
      (L.of_frame (finaliseEndpointCancelStep_keepsIpcInvariantFull s en q t ep tcb ⟨L.1, L.2.1⟩ hT
        hE hC).1 (FinaliseFrame.storeEndpointBlockedCancelled s en q t ep tcb L.2.1))
      (storeEndpointBlockedCancelled_savedRegsKeptExcept s en q t ep tcb L.2.1)
      (blocked h hT (blockedOnQueueSide_notReady (endpointBlockedCancellable_parts hC).1))
  · intro s t tcb h hT hS hO hI hId
    have R := h.1; have L := h.2.1
    exact step h ⟨R.1.trans (finaliseSuspend_runQueueEntryStage s t tcb hT hS hO hId),
        R.2.trans R.1.1 (descheduleAtThenWrite_readyKeptStage s t _ finalisedSuspendMark
          fun _ h => h)⟩
      (L.of_frame (finaliseSuspendStep_keepsIpcInvariantFull s t tcb ⟨L.1, L.2.1⟩ hT hS hO hI hId).1
        (FinaliseFrame.suspend s t L.2.1))
      (finaliseSuspend_savedRegsKeptExcept s t L.2.1) none
  · intro s t h
    have R := h.1; have L := h.2.1
    exact step h (readyEntry_stage R (SystemState.RunQueueStage.of_frameLive
      (st' := finaliseThreadReleaseCores s t)
      (finaliseThreadReleaseCores_objects s t)
      (by rw [finaliseThreadReleaseCores_scheduler]) (by rw [finaliseThreadReleaseCores_scheduler])
      (fun c u hU => by
        rw [finaliseThreadReleaseCores_machine] at hU
        unfold MachineState.releaseThread at hU
        rw [MachineState.releaseThreadOnCores_residentOnCore] at hU
        split at hU
        · cases hU
        · exact Or.inl hU)
      (by rw [finaliseThreadReleaseCores_scheduler])
      (by rw [finaliseThreadReleaseCores_scheduler])))
      (L.of_frame (finaliseReleaseStep_keepsIpcInvariantFull s t ⟨L.1, L.2.1⟩).1
        (FinaliseFrame.releaseCores s t L.2.1))
      (.of_objects_eq (finaliseThreadReleaseCores_objects s t)) none
  · intro s s1 x sc rid r h hSc hRep hR hN hS s₀ h₀ hA hS₀
    have R := h.1; have L := h.2.1
    have hI := finaliseUnstackStep_keepsIpcInvariantFull s s1 x sc rid r ⟨L.1, L.2.1⟩ hSc hRep hR
      hN hS s₀ ⟨h₀.2.1.1, h₀.2.1.2.1⟩ hA hS₀
    exact step h (readyEntry_stage R ((storeObject_replyOver_runQueueStage hR hS).trans
        (updateSchedContext_runQueueStage s1 ⟨x.val⟩ _)))
      ⟨hI.1, hI.2, finaliseUnstack_keepsLentContextHeads L.2.1 L.1.donationOwnerValid L.2.2 hSc
        (finaliseSchedContextUnbind_unbound h₀.2.1.2.1 hA (hS₀ ▸ hSc)) hR hN hS⟩
      ((savedRegsKeptExcept.storeObject_replyOver L.2.1 hR hS).trans
        (.updateSchedContext s1 _ _ (storeObject_preserves_objects_invExt s s1 _ _ L.2.1 hS))) none
  · intro s x r c t h hO hC hT hF
    have R := h.1; have L := h.2.1
    obtain ⟨-, -, -, -, ⟨ep, rt, hSt⟩, -⟩ := replyCallerFinalisable_parts hF
    exact step h (readyEntry_stage R ((cancelIpcBlockingReclaimed_runQueueStage s c t).trans
        (finaliseReplyRevert_runQueueStage _ _)))
      (finaliseReplyStep_keepsIpcInvariantFull s x r c t L hO hC hT hF)
      (finaliseReplyCancel_savedRegsKeptExcept s c t L.2.1)
      (blocked h hT (by rw [hSt]; exact fun y => by cases y))
  · intro s s1 x tid t h hT hC e
    have R := h.1; have L := h.2.1
    have hI := finaliseUnstashStep_keepsIpcInvariantFull s s1 x tid t ⟨L.1, L.2.1⟩ hT hC e
    subst e
    exact step h (readyEntry_stage R
        (SystemState.RunQueueStage.updateTcb s tid (f := TCB.stashCleared) (fun _ _ => rfl)))
      ⟨hI.1, hI.2, L.2.2.of_loanWrite (FinaliseFrame.updateTcb s tid _ L.2.1).loan⟩
      (.updateTcb s tid _ L.2.1 (fun _ => rfl)) none
  · refine ⟨fun s t h => ?_, fun s c h => ?_⟩
    · have R := h.1; have L := h.2.1
      exact step h (readyEntry_stage R (SystemState.cancelYieldTo_runQueueStage s t))
        (L.of_frame (cancelYieldTo_preserves_ipcInvariantFull s t L.2.1 L.1)
          (FinaliseFrame.cancelYieldTo s t L.2.1))
        (cancelYieldTo_savedRegsKeptExcept s t L.2.1) none
    · have R := h.1; have L := h.2.1
      exact step h (readyEntry_stage R (SystemState.completeYieldFrom_runQueueStage s c))
        (L.of_frame (completeYieldFrom_preserves_ipcInvariantFull s c L.2.1 L.1)
          (FinaliseFrame.completeYieldFrom s c L.2.1))
        (completeYieldFrom_savedRegsKeptExcept L.2.1)
        (fun _ ⟨_, _, hS, hC, hu⟩ => hu ▸ offCoreFree_of_yieldFromSince B R.1 hS hC)
  · intro s w x t h hT _ hS
    have R := h.1; have L := h.2.1
    exact step h (readyEntry_stage R (orphanReplyWaiter_runQueueStage hT hS))
      (L.of_frame (orphanReplyWaiter_preserves_ipcInvariantFull L.1 hT hS)
        (FinaliseFrame.orphanReplyWaiter s w x L.2.1))
      ((savedRegsKeptExcept.of_map fun y => by
          by_cases hy : w.toObjId = y.toObjId
          · rw [← ThreadId.toObjId_injective _ _ hy, SystemState.mapTcbInPlace_getTcb?_self,
              Option.map_map]; rfl
          · rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hy]).trans
        (.of_replyLinks (SystemState.unlinkReplyWaiter_objectsAgreeOffReplyLinks _ _ _))) none
  · intro s x r c t h _ hLk hX _ hT hA
    have R := h.1; have L := h.2.1
    exact step h (readyEntry_stage R (finaliseReplyUnheldPop_runQueueStage s r c))
      (finaliseUnheldStep_keepsFinaliseLoanBundle s x r c t L hLk hX hT hA)
      (.of_finaliseReplyUnheldPop s r c L.2.1) none
  · intro s _ _ _ t h _ _ _ _
    have R := h.1; have L := h.2.1
    exact step h (readyEntry_stage R (cutCancelledCallerHead_runQueueStage s t))
      (cutCancelledCallerHead_preserves_finaliseLoanBundle s t L)
      (savedRegsKeptExcept.of_map
        (cutCancelledCallerHead_getTcb?_map s t TCB.registerContext (fun _ => rfl) L.2.1)) none

end

/-! ### The delete's register-free pieces -/

namespace savedRegsKeptExcept

variable {W : SeLe4n.ThreadId → Prop}

/-- **Slot by slot, threads included**: every slot keeps its object, holds no TCB
on either side, or holds a TCB on both with the same saved registers. -/
theorem of_slotsTcb {pre post : SystemState}
    (h : ∀ k : SeLe4n.ObjId, post.objects[k]? = pre.objects[k]? ∨
      ((∀ x : TCB, pre.objects[k]? ≠ some (.tcb x)) ∧ ∀ x : TCB, post.objects[k]? ≠ some (.tcb x)) ∨
      ∃ x y : TCB, pre.objects[k]? = some (.tcb x) ∧ post.objects[k]? = some (.tcb y) ∧
        y.registerContext = x.registerContext) :
    savedRegsKeptExcept W pre post := fun t _ => by
  have a : ∀ st : SystemState, (∀ x : TCB, st.objects[t.toObjId]? ≠ some (.tcb x)) →
      st.getTcb? t = none := fun st h0 => by
    cases e : st.getTcb? t with
    | none => rfl
    | some x => exact absurd ((SystemState.getTcb?_eq_some_iff _ _ _).mp e) (h0 x)
  unfold SystemState.savedRegs
  rcases h t.toObjId with e | hN | ⟨x, y, hx, hy, hr⟩
  · unfold SystemState.getTcb?; rw [e]
  · rw [a _ hN.1, a _ hN.2]
  · rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hx, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hy]
    exact congrArg some hr

/-- The slot-link writes rewrite CNodes and threads' space-slot links. -/
theorem of_linkReach {st₀ st : SystemState} (hR : SystemState.linkReach st₀ st)
    (hInv : st₀.objects.invExt) : savedRegsKeptExcept W st₀ st :=
  of_slotsTcb fun oid => by
    rcases hR.agree hInv oid with e | ⟨_, _, ha, hb, _⟩ | ⟨t, t', ha, hb, hw⟩
    · exact .inl e
    · exact .inr (.inl ⟨fun x hx => (by rw [ha] at hx; cases hx), fun x hx => (by rw [hb] at hx; cases hx)⟩)
    · exact .inr (.inr ⟨t, t', ha, hb, TCB.proj_eq_of_withoutLinks_eq TCB.registerContext hw⟩)

/-- **The delete**: a slot cleared in a CNode or a thread's space slots, then the
derivation tree spliced with its slot links. -/
theorem of_cspaceDeleteSlot {st st' : SystemState} {addr : CSpaceAddr} (hInv : st.objects.invExt)
    (hD : cspaceDeleteSlot addr st = .ok ((), st')) : savedRegsKeptExcept W st st' := by
  obtain ⟨stC, hCore, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' hD
  have hIC := cspaceDeleteSlotCore_invExt st stC addr hInv hCore
  have k1 : savedRegsKeptExcept W st stC := of_slotsTcb fun k => by
    by_cases hk : k = addr.cnode
    · subst hk
      rcases cspaceDeleteSlotCore_ok_cases hCore with ⟨cn, hO, hS⟩ | ⟨t, hO, hS⟩
      · refine .inr (.inl ⟨fun x hx => (by rw [hO] at hx; cases hx), fun x hx => ?_⟩)
        rw [storeObject_objects_eq' st _ _ _ hInv hS] at hx; cases hx
      · exact .inr (.inr ⟨t, _, hO, storeObject_objects_eq' st _ _ _ hInv hS, rfl⟩)
    · rcases cspaceDeleteSlotCore_ok_cases hCore with ⟨_, _, hS⟩ | ⟨_, _, hS⟩ <;>
        exact .inl (storeObject_objects_ne st stC _ k _ hk hInv hS)
  exact k1.trans ((of_objects_eq (pre := stC) (post := { stC with cdt := stC.cdt.spliceNode addr })
    rfl).trans (of_linkReach (spliceDeletedCdtNode_reach stC addr) hIC))

/-- A write of VSpace roots alone. -/
theorem of_vspaceRootOnlyWrite {st st' : SystemState} (h : vspaceRootOnlyWrite st st') :
    savedRegsKeptExcept W st st' :=
  of_slots fun oid => by
    rcases h oid with e | ⟨⟨r, hr⟩, ⟨r', hr'⟩⟩
    · exact .inl e
    · exact .inr ⟨fun x hx => (by rw [hr] at hx; cases hx), fun x hx => (by rw [hr'] at hx; cases hx)⟩

/-- The registry's one object write, an endpoint's service record. -/
theorem of_serviceRecordRewrite {st st' : SystemState} (hInv : st.objects.invExt)
    (hW : ServiceRecordRewrite st.objects st'.objects) : savedRegsKeptExcept W st st' :=
  of_slots fun oid => by
    rcases hW.lookup hInv oid with e | ⟨_, _, h0, h1⟩
    · exact .inl e
    · exact .inr ⟨fun x hx => (by rw [h0] at hx; cases hx), fun x hx => (by rw [h1] at hx; cases hx)⟩

/-- **The registration's release**: at most one revocation. -/
theorem of_releaseFinalRegistration (target : Nat) (st : SystemState) (hInv : st.objects.invExt) :
    savedRegsKeptExcept W st (releaseFinalRegistration target st) :=
  (releaseFinalRegistration_closed (fun s => savedRegsKeptExcept W st s ∧ s.objects.invExt)
    (fun _ _ _ hs hR =>
      have hW := revokeService_serviceRecordRewrite hR
      ⟨hs.1.trans (of_serviceRecordRewrite hs.2 hW), hW.invExt hs.2⟩)
    target st ⟨refl st, hInv⟩).1

end savedRegsKeptExcept

/-- A thread no core holds is free of every core. -/
theorem offCoreFree_of_notHeld {e : CoreId} {st : SystemState} {t : SeLe4n.ThreadId}
    (h : threadHeldOnSomeCore st t = false) : offCoreFree e st t := by
  unfold threadHeldOnSomeCore at h
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨⟨hC, -⟩, hR⟩ := h
  intro d _
  refine ⟨fun hd => ?_, (MachineState.residentOnSomeCore_eq_false_iff _ _).mp hR d⟩
  have := (threadCurrentOnSomeCore_iff st t).mpr ⟨d, hd⟩
  rw [hC] at this; cases this

/-- **The core release**: the retire keeps every thread's saved registers but
those of a thread it removes, which no core held. -/
theorem retireFinalObject_savedRegs (e ec : CoreId) (target recorder : Nat) (st : SystemState)
    (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    (retireFinalObject ec target recorder st).savedRegs t = st.savedRegs t ∨ offCoreFree e st t := by
  unfold SystemState.savedRegs
  cases hT : st.getTcb? t with
  | some x =>
    rcases retireFinalObject_tcb_kept_or_quiescent ec target recorder st hInv
        ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) with e' | ⟨-, hId, -, -, hH⟩
    · left; unfold SystemState.getTcb?; rw [e']; unfold SystemState.getTcb? at hT; rw [hT]
    · right
      have : x.tid = t := SeLe4n.ThreadId.ext hId
      exact this ▸ offCoreFree_of_notHeld hH
  | none =>
    left
    cases hP : (retireFinalObject ec target recorder st).getTcb? t with
    | none => rfl
    | some y =>
      have := retireFinalObject_back ec target recorder st hInv
        ((SystemState.getTcb?_eq_some_iff _ _ _).mp hP) (fun U h => by cases h)
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr this] at hT; cases hT

/-! ### The finalising delete and its chains -/

section
open SeLe4n.Kernel.Lifecycle.Suspend

/-- **A finalising delete writes the saved registers only of threads free at the
entry's start, or of threads no core holds after it**: the delete, the page
teardown and the registration's release write none, the finalisation writes
free threads (`finaliseFinalObject_savedRegsWrittenFree`), and the retire removes
only a thread no core holds (`retireFinalObject_savedRegs`), which leaves the
scheduler and the machine as they were. -/
theorem cspaceDeleteSlotFinalising_savedRegsWritten {e ec : CoreId} {addr : CSpaceAddr}
    {st s s' : SystemState} (B : FinaliseCensusBase st)
    (hR : SystemState.RunQueueEntryStage st s ∧ readyKeptStage (fun _ => False) st s)
    (hB : finalisingDeleteBundle s) (h : cspaceDeleteSlotFinalising ec addr s = .ok ((), s')) :
    ∀ t, s'.savedRegs t = s.savedRegs t ∨ offCoreFree e st t ∨ offCoreFree e s' t := by
  obtain ⟨st1, st2, hD, hF, rfl⟩ := cspaceDeleteSlotFinalising_ok ec addr s s' h
  have hI1 := cspaceDeleteSlot_preserves_objects_invExt s st1 addr hB.1.2.1 hD
  obtain ⟨hI2, hV, -⟩ := finaliseDestroyedCapabilities_ok_frame ec _ _ st1 st2 hI1 hF
  have hB3 := releaseFinalRegistration_closed finalisingDeleteBundle
    (fun _ _ _ hs hR => revokeService_preserves_finalisingDeleteBundle hs hR)
    (slotRetireTarget s addr.cnode addr.slot) st2
    (cspaceDeleteSlotTeardown_preserves_finalisingDeleteBundle hB hD hF)
  have hR3 := readyEntry_stage hR
    (((cspaceDeleteSlot_runQueueStage hD).trans (finaliseDestroyedCapabilities_runQueueStage hF)).trans
      (releaseFinalRegistration_runQueueStage (slotRetireTarget s addr.cnode addr.slot) st2))
  have k3 : savedRegsKeptExcept (fun _ => False) s
      (releaseFinalRegistration (slotRetireTarget s addr.cnode addr.slot) st2) :=
    ((savedRegsKeptExcept.of_cspaceDeleteSlot hB.1.2.1 hD).trans
      (savedRegsKeptExcept.of_vspaceRootOnlyWrite hV)).trans
      (savedRegsKeptExcept.of_releaseFinalRegistration _ st2 hI2)
  have w4 := finaliseFinalObject_savedRegsWrittenFree (e := e) B hR3 hB3
    (slotRetireTarget s addr.cnode addr.slot)
  have hI4 := (finaliseFinalObject_preserves_finalisingDeleteBundle
    (slotRetireTarget s addr.cnode addr.slot) _ hB3).1.2.1
  intro t
  rcases retireFinalisedObject_cases ec (slotRetireTarget s addr.cnode addr.slot)
      (slotRetireRecorder s addr.cnode addr.slot) st2 with ⟨-, hE⟩ | ⟨-, hE⟩
  · rw [hE]
    left
    have k2 : savedRegsKeptExcept (fun _ => False) s st2 :=
      (savedRegsKeptExcept.of_cspaceDeleteSlot hB.1.2.1 hD).trans
        (savedRegsKeptExcept.of_vspaceRootOnlyWrite hV)
    refine Eq.trans ?_ (k2 t id)
    simp only [SystemState.savedRegs, SystemState.getTcb?, retireIrqNode_objects]
  rw [hE]
  have hFr := retireFinalObject_fields ec (slotRetireTarget s addr.cnode addr.slot)
    (slotRetireRecorder s addr.cnode addr.slot)
    (finaliseFinalObject (slotRetireTarget s addr.cnode addr.slot)
      (releaseFinalRegistration (slotRetireTarget s addr.cnode addr.slot) st2))
  rcases retireFinalObject_savedRegs e ec _ (slotRetireRecorder s addr.cnode addr.slot) _ hI4 t
    with r | r
  · rcases w4 t with w | w
    · exact .inl (r.trans (w.trans (k3 t id)))
    · exact .inr (.inl w)
  · refine .inr (.inr fun d hd => ?_)
    rw [hFr.2.1, hFr.2.2]; exact r d hd

end

/-- **The census extends over a step** that writes only threads free at the
entry's start or held on no other core after it: a thread another core holds
after the step was held there before it and at the start. -/
theorem savedRegsKeptOffCore_extend {e : CoreId} {st s s' : SystemState}
    (h : savedRegsKeptOffCore e st s) (hS : stepCovers e s s') (hC : stepCovers e st s')
    (hW : ∀ t, s'.savedRegs t = s.savedRegs t ∨ offCoreFree e st t ∨ offCoreFree e s' t) :
    savedRegsKeptOffCore e st s' := fun d hd t ht => by
  rcases hW t with w | w | w
  · exact w.trans (h d hd t (ht.imp (hS.currentKept d hd t) (hS.residentKept d hd t)))
  · exfalso
    rcases ht with x | x
    · exact (w d hd).1 (hC.currentKept d hd t x)
    · exact (w d hd).2 (hC.residentKept d hd t x)
  · exfalso
    rcases ht with x | x
    · exact (w d hd).1 x
    · exact (w d hd).2 x

/-- What the census carries along a delete chain: coverage and the delete's
bundle from the start, the readiness frame, and the census itself. -/
def finaliseCensusChain (e : CoreId) (st s : SystemState) : Prop :=
  coversWithDeleteBundle e st s ∧
    (SystemState.RunQueueEntryStage st s ∧ readyKeptStage (fun _ => False) st s) ∧
    savedRegsKeptOffCore e st s

namespace finaliseCensusChain

variable {e : CoreId} {st : SystemState}

theorem start (hB : finalisingDeleteBundle st) : finaliseCensusChain e st st :=
  ⟨⟨stepCovers_refl e st, hB⟩, readyEntry_refl st, savedRegsKeptOffCore_refl e st⟩

/-- A finalising delete extends the chain. -/
theorem delete (B : FinaliseCensusBase st) {ec : CoreId} {c : CSpaceAddr} {s s' : SystemState}
    (hQ : finaliseCensusChain e st s) (hD : cspaceDeleteSlotFinalising ec c s = .ok ((), s')) :
    finaliseCensusChain e st s' :=
  have hC := hQ.1.delete hD
  ⟨hC, cspaceDeleteSlotFinalising_readyEntry hQ.2.1 hD,
    savedRegsKeptOffCore_extend hQ.2.2 (cspaceDeleteSlotFinalising_stepCovers e ec c s s' hQ.1.2 hD).1
      hC.1 (cspaceDeleteSlotFinalising_savedRegsWritten B hQ.2.1 hQ.1.2 hD)⟩

/-- A finalisation extends the chain. -/
theorem finalise (B : FinaliseCensusBase st) (d : Nat) {s : SystemState}
    (hQ : finaliseCensusChain e st s) : finaliseCensusChain e st (finaliseFinalObject d s) :=
  have hC := hQ.1.finalise d
  ⟨hC, finaliseFinalObject_readyEntry d hQ.2.1,
    savedRegsKeptOffCore_extend hQ.2.2 (finaliseFinalObject_stepCovers e d s hQ.1.2.1.2.1).1 hC.1
      (fun t => (finaliseFinalObject_savedRegsWrittenFree B hQ.2.1 hQ.1.2 d t).imp_right .inl)⟩

end finaliseCensusChain

/-- WS-ZA ZA6.24: **the zombie delete writes the saved registers of no thread
another core holds**, one finalising delete or finalisation at a time. -/
theorem cspaceDeleteSlotZombie_savedRegsKeptOffCore {e ec : CoreId} {addr : CSpaceAddr}
    {st st' : SystemState} (B : FinaliseCensusBase st) (hB : finalisingDeleteBundle st)
    (h : cspaceDeleteSlotZombie ec addr st = .ok ((), st')) : savedRegsKeptOffCore e st st' :=
  (cspaceDeleteSlotZombie_closed (finaliseCensusChain e st)
    (fun _ _ _ hQ hD => hQ.delete B hD) (fun d _ hQ => hQ.finalise B d)
    (.start hB) h).2.2

/-- WS-ZA ZA6.24: **the finalising revocation writes the saved registers of no
thread another core holds**, one finalising delete at a time. -/
theorem cspaceRevokeCdtFinalising_savedRegsKeptOffCore {e ec : CoreId} {addr : CSpaceAddr}
    {st st' : SystemState} (B : FinaliseCensusBase st) (hB : finalisingDeleteBundle st)
    (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) : savedRegsKeptOffCore e st st' :=
  (cspaceRevokeCdtFinalising_closed (finaliseCensusChain e st)
    (fun _ _ _ hQ hD => hQ.delete B hD) (fun d _ hQ => hQ.finalise B d)
    (.start hB) h).2.2

end SeLe4n.Kernel
