-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.Operations

/-!
# A scheduling context donated through a notification

seL4-MCS's `maybeDonateSchedContext` (`notification.c`): when a thread takes a
notification's word — `completeSignal`, and `sendSignal`'s wake of a waiter or
of a bound receiver — and the thread holds no scheduling context while the
notification's context is bound to no thread, the context is donated to the
thread (`schedContext_donate`) and resumed (`schedContext_resume`).

The owner's decision D19 records the donation as the receiving thread's
`.bound` binding, with the notification link kept on the context.  seL4's guard
is all the donation asks (`schedContextDonateAdmitted`): the thread holds no
context and the context is bound to no thread.  Then the bind's writes are made
(`schedContextBindPerform`): the context names the thread, the thread is bound,
a parked runnable thread is placed on its home core, and the context waits on
that core's release queue for a head not yet released (`schedContext_resume`).
When the guard fails the state is unchanged, as seL4 donates nothing.  The
bind's further refusals (a context heading a reply stack, a thread owed a
context by a live reply stack) are `SchedContext_Bind`'s decode, which seL4's
donation does not ask; where they also pass the donation is the bind's ok-state
(`maybeDonateSchedContext_eq_bind`).

The compiled form (`maybeDonateSchedContextFast`) asks the guard before any
write and makes the writes in place, so a donation allocates nothing.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **seL4-MCS `maybeDonateSchedContext`**: the context bound to notification
`n`, donated to `tid` as its `.bound` binding when seL4's guard holds — the
thread holds no context and the context is bound to no thread
(`schedContextDonateAdmitted`) — and the bind's writes made
(`schedContextBindPerform`); else the state unchanged, as seL4 does nothing. -/
def maybeDonateSchedContext (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) :
    SystemState :=
  match st.getNotification? n with
  | none => st
  | some ntfn =>
    match ntfn.schedContext with
    | none => st
    | some s =>
      match s.toObjId.toValid?, tid.toValid? with
      | some vS, some vT =>
        if SchedContextOps.schedContextDonateAdmitted st vS vT then
          SchedContextOps.schedContextBindPerform st vS vT
        else st
      | _, _ => st

/-- **The donation is the identity or the bind's writes under seL4's guard**,
the context being the notification's: every family lemma of the donation is the
identity's and the perform's. -/
theorem maybeDonateSchedContext_cases (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) :
    maybeDonateSchedContext st n tid = st ∨
      ∃ (vS : SeLe4n.ValidObjId) (vT : SeLe4n.ValidThreadId), vT.val = tid ∧
        (∃ ntfn s, st.getNotification? n = some ntfn ∧ ntfn.schedContext = some s ∧
          s.toObjId = vS.val) ∧
        SchedContextOps.schedContextDonateAdmitted st vS vT = true ∧
        maybeDonateSchedContext st n tid = SchedContextOps.schedContextBindPerform st vS vT := by
  unfold maybeDonateSchedContext
  split
  · exact Or.inl rfl
  rename_i ntfn hN
  split
  · exact Or.inl rfl
  rename_i s hS
  split
  · rename_i vS vT hSv hT
    split
    · rename_i hA
      refine Or.inr ⟨vS, vT, ?_, ⟨ntfn, s, hN, hS, ?_⟩, hA, rfl⟩
      · unfold SeLe4n.ThreadId.toValid? at hT
        split at hT
        · cases hT
        · cases hT; rfl
      · unfold SeLe4n.ObjId.toValid? at hSv
        split at hSv
        · cases hSv
        · cases hSv; rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- **A property every guarded perform for `tid` carries, and the identity, the
donation carries.** -/
theorem maybeDonateSchedContext_induct (P : SystemState → SystemState → Prop)
    (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (hId : P st st)
    (hDonate : ∀ (vS : SeLe4n.ValidObjId) (vT : SeLe4n.ValidThreadId), vT.val = tid →
      SchedContextOps.schedContextDonateAdmitted st vS vT = true →
      P st (SchedContextOps.schedContextBindPerform st vS vT)) :
    P st (maybeDonateSchedContext st n tid) := by
  rcases maybeDonateSchedContext_cases st n tid with h | ⟨vS, vT, hT, _, hA, h⟩
  · rw [h]; exact hId
  · rw [h]; exact hDonate vS vT hT hA

/-- **seL4's donation guard, as the footprints read it**: the notification is
bound to a context, the context to no thread, and the receiver to no context
(`schedContextDonateAdmitted`).  The lock sets of the arms that donate name the
context and its receiver's home core exactly when this holds. -/
def signalDonationGuard (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) : Bool :=
  match st.getNotification? n with
  | none => false
  | some ntfn =>
    match ntfn.schedContext with
    | none => false
    | some s =>
      match s.toObjId.toValid?, tid.toValid? with
      | some vS, some vT => SchedContextOps.schedContextDonateAdmitted st vS vT
      | _, _ => false

/-- **Where the guard fails the donation writes nothing.** -/
theorem maybeDonateSchedContext_of_guard_false {st : SystemState} {n : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} (h : signalDonationGuard st n tid = false) :
    maybeDonateSchedContext st n tid = st := by
  unfold signalDonationGuard at h
  unfold maybeDonateSchedContext
  cases hN : st.getNotification? n with
  | none => rfl
  | some ntfn =>
    rw [hN] at h
    simp only at h ⊢
    cases hS : ntfn.schedContext with
    | none => rfl
    | some s =>
      rw [hS] at h
      simp only at h ⊢
      cases hV : s.toObjId.toValid? <;> cases hT : tid.toValid? <;> simp_all

/-- seL4's guard reads, of the context, whether it names a thread, and of the
receiver, whether its binding names a context. -/
theorem schedContextDonateAdmitted_eq_any (st : SystemState) (vS : SeLe4n.ValidObjId)
    (vT : SeLe4n.ValidThreadId) :
    SchedContextOps.schedContextDonateAdmitted st vS vT =
      (((st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val)).map
          (·.boundThread)).any Option.isNone &&
        ((st.getTcb? vT.val).map (·.schedContextBinding.scId?)).any Option.isNone) := by
  unfold SchedContextOps.schedContextDonateAdmitted
  have hV := SystemState.getSchedContextWitnessed?_val st (SeLe4n.SchedContextId.ofObjId vS.val)
  split
  · rename_i hW
    rw [hW] at hV
    rw [← hV]; rfl
  · rename_i sc _ hW
    rw [hW] at hV
    rw [← hV]
    simp only [Option.map_some, Option.any_some]
    cases hB : sc.boundThread with
    | some t => simp
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.isNone_none,
        Bool.true_and]
      cases st.getTcb? vT.val with
      | none => rfl
      | some tcb =>
        simp only [Option.map_some, Option.any_some]
        cases tcb.schedContextBinding <;> rfl

/-- **The guard reads three links**: the notification's context, the context's
thread and the receiver's context.  A step keeping all three keeps the guard. -/
theorem signalDonationGuard_congr {st st' : SystemState} {n : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId}
    (hN : (st'.getNotification? n).map (·.schedContext) =
      (st.getNotification? n).map (·.schedContext))
    (hS : ∀ s, (st'.getSchedContext? s).map (·.boundThread) =
      (st.getSchedContext? s).map (·.boundThread))
    (hT : (st'.getTcb? tid).map (·.schedContextBinding.scId?) =
      (st.getTcb? tid).map (·.schedContextBinding.scId?)) :
    signalDonationGuard st' n tid = signalDonationGuard st n tid := by
  unfold signalDonationGuard
  cases h1 : st.getNotification? n with
  | none =>
    rw [h1] at hN
    cases h2 : st'.getNotification? n with
    | none => rfl
    | some _ => rw [h2] at hN; cases hN
  | some ntfn =>
    rw [h1] at hN
    cases h2 : st'.getNotification? n with
    | none => rw [h2] at hN; cases hN
    | some ntfn' =>
      rw [h2] at hN
      simp only [Option.map_some, Option.some.injEq] at hN
      simp only [hN]
      cases ntfn.schedContext with
      | none => rfl
      | some s =>
        simp only
        cases s.toObjId.toValid? with
        | none => rfl
        | some vS =>
          cases hTv : tid.toValid? with
          | none => rfl
          | some vT =>
            simp only
            rw [schedContextDonateAdmitted_eq_any, schedContextDonateAdmitted_eq_any, hS,
              SeLe4n.ThreadId.toValid?_some_val_eq tid vT hTv, hT]

/-- **The cores a donation writes**: the receiver's home core where seL4's
guard holds, and none where it does not. -/
def signalDonationCores (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) :
    List Concurrency.CoreId :=
  if signalDonationGuard st n tid then [determineTargetCore st tid] else []

/-- **The notification bound to `tid`** (`TCB.boundNotification`), as the id
its code names; `⟨0⟩` for a thread with none, which a receive never reads
(`receiveCompletesSignal` is `false` there). -/
@[inline] def receiverBoundNotification (st : SystemState) (tid : SeLe4n.ThreadId) :
    SeLe4n.ObjId :=
  match st.getTcb? tid with
  | some t => ⟨t.boundNotificationCode - 1⟩
  | none => ⟨0⟩

/-- **The context bound to notification `n`**, if any. -/
def notificationContext? (st : SystemState) (n : SeLe4n.ObjId) : Option SeLe4n.SchedContextId :=
  (st.getNotification? n).bind (·.schedContext)

/-- **The context a donation writes**, where seL4's guard holds. -/
def signalDonationContext? (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) :
    Option SeLe4n.SchedContextId :=
  if signalDonationGuard st n tid then notificationContext? st n else none

/-- The context a donation writes is the notification's bound context. -/
theorem notificationContext?_of_signalDonationContext? {st : SystemState} {n : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {s : SeLe4n.SchedContextId}
    (h : signalDonationContext? st n tid = some s) : notificationContext? st n = some s := by
  unfold signalDonationContext? at h
  split at h
  · exact h
  · cases h

/-- **Where the bind's checks also pass, the donation is the bind's ok-state**,
so the bind's own family lemmas apply to it. -/
theorem maybeDonateSchedContext_eq_bind {st : SystemState} {n : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {vS : SeLe4n.ValidObjId} {vT : SeLe4n.ValidThreadId}
    (h : maybeDonateSchedContext st n tid = SchedContextOps.schedContextBindPerform st vS vT)
    (hA : SchedContextOps.schedContextBindAdmitted st vS vT = true) :
    SchedContextOps.schedContextBind vS vT st = .ok ((), maybeDonateSchedContext st n tid) := by
  rw [h]; exact SchedContextOps.schedContextBind_of_admitted st vS vT hA

/-- **The compiled donation**, the ids passed as their codes: seL4's guard
(`schedContextDonateAdmitted`) asked before any write, then the bind's writes in
place (`schedContextBindPerform`, compiled as its `Impl`).  A context code at or
past `2 ^ 62` — which no object store holds — takes the specification, so no
code is a heap number. -/
@[noinline] def maybeDonateSchedContextFast (st : SystemState) (nCode tCode : Nat) :
    SystemState :=
  match st.getNotification? ⟨nCode⟩ with
  | none => st
  | some ntfn =>
    let sCode := ntfn.schedContextCode
    if sCode = 0 then st
    else if sCode < 2 ^ 62 then
      if hS : (⟨sCode - 1⟩ : SeLe4n.ObjId) = SeLe4n.ObjId.sentinel then st
      else if hT : (⟨tCode⟩ : SeLe4n.ThreadId) = SeLe4n.ThreadId.sentinel then st
      else if SchedContextOps.schedContextDonateAdmitted st ⟨⟨sCode - 1⟩, hS⟩ ⟨⟨tCode⟩, hT⟩ then
        SchedContextOps.schedContextBindPerform st ⟨⟨sCode - 1⟩, hS⟩ ⟨⟨tCode⟩, hT⟩
      else st
    else maybeDonateSchedContext st ⟨nCode⟩ ⟨tCode⟩

/-- **The compiled donation is the donation.** -/
theorem maybeDonateSchedContextFast_eq (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) :
    maybeDonateSchedContextFast st n.val tid.val = maybeDonateSchedContext st n tid := by
  unfold maybeDonateSchedContextFast
  cases hN : st.getNotification? ⟨n.val⟩ with
  | none =>
    unfold maybeDonateSchedContext
    rw [show (⟨n.val⟩ : SeLe4n.ObjId) = n from rfl] at hN
    rw [hN]
  | some ntfn =>
    have hN' : st.getNotification? n = some ntfn := hN
    simp only
    by_cases h0 : ntfn.schedContextCode = 0
    · unfold maybeDonateSchedContext
      simp only [h0, ↓reduceIte, hN', Notification.schedContext, SeLe4n.SchedContextId.ofOptCode]
    by_cases hW : ntfn.schedContextCode < 2 ^ 62
    · simp only [h0, hW, ↓reduceIte]
      unfold maybeDonateSchedContext
      obtain ⟨k, hk⟩ : ∃ k, ntfn.schedContextCode = k + 1 :=
        ⟨ntfn.schedContextCode - 1, by omega⟩
      simp only [hN', Notification.schedContext, hk, SeLe4n.SchedContextId.ofOptCode, Nat.add_sub_cancel,
        SeLe4n.SchedContextId.toObjId, SeLe4n.SchedContextId.toNat, SeLe4n.ObjId.ofNat,
        SeLe4n.ObjId.toValid?, SeLe4n.ThreadId.toValid?]
      by_cases hS : (⟨k⟩ : SeLe4n.ObjId) = SeLe4n.ObjId.sentinel
      · simp only [hS, ↓reduceDIte]
      by_cases hT : (⟨tid.val⟩ : SeLe4n.ThreadId) = SeLe4n.ThreadId.sentinel
      · have hT' : tid = SeLe4n.ThreadId.sentinel := hT
        simp only [hS, hT, hT', ↓reduceDIte]
      have hT' : ¬ tid = SeLe4n.ThreadId.sentinel := hT
      simp only [hS, hT, hT', ↓reduceDIte]
    · simp only [h0, hW, ↓reduceIte]


/-! ### The donation writes no register -/

/-- The compiled donation at a thread named by its code. -/
theorem maybeDonateSchedContextFast_eq_code (st : SystemState) (n : SeLe4n.ObjId) (k : Nat) :
    maybeDonateSchedContextFast st n.val k = maybeDonateSchedContext st n ⟨k⟩ :=
  maybeDonateSchedContextFast_eq st n ⟨k⟩

/-- **Every thread's register file agrees** between two states. -/
def registersAgree (st' st : SystemState) : Prop :=
  ∀ t : SeLe4n.ThreadId, (st'.getTcb? t).map TCB.registerContext = (st.getTcb? t).map TCB.registerContext

namespace registersAgree

theorem refl (st : SystemState) : registersAgree st st := fun _ => rfl

theorem trans {a b c : SystemState} (h₁ : registersAgree a b) (h₂ : registersAgree b c) :
    registersAgree a c := fun t => (h₁ t).trans (h₂ t)

private theorem getTcb?_map_of_objects {st' st : SystemState} (t : SeLe4n.ThreadId)
    (w : KernelObject → KernelObject) (hw : ∀ x, (∃ y, w x = .tcb y) ↔ ∃ y, x = .tcb y)
    (hr : ∀ x y, w x = .tcb y → ∃ y', x = .tcb y' ∧ y.registerContext = y'.registerContext)
    (h : (st'.objects[t.toObjId]?).map w = (st.objects[t.toObjId]?).map w) :
    (st'.getTcb? t).map TCB.registerContext = (st.getTcb? t).map TCB.registerContext := by
  unfold SystemState.getTcb?
  cases h1 : st'.objects[t.toObjId]? with
  | none =>
    rw [h1] at h
    cases h2 : st.objects[t.toObjId]? with
    | none => rfl
    | some o => rw [h2] at h; cases h
  | some o1 =>
    rw [h1] at h
    cases h2 : st.objects[t.toObjId]? with
    | none => rw [h2] at h; cases h
    | some o2 =>
      rw [h2] at h
      simp only [Option.map_some, Option.some.injEq] at h
      cases o1 with
      | tcb a =>
        obtain ⟨y, hy⟩ := (hw (.tcb a)).mpr ⟨a, rfl⟩
        rw [h] at hy
        obtain ⟨b, rfl, hb⟩ := hr _ _ hy
        obtain ⟨b', hb', ha⟩ := hr _ _ (h ▸ hy)
        cases hb'
        simp only [Option.map_some]
        rw [← h] at hy
        obtain ⟨a', ha', hab⟩ := hr _ _ hy
        cases ha'
        rw [← hab, hb]
      | _ =>
        cases o2 with
        | tcb b =>
          exfalso
          obtain ⟨y, hy⟩ := (hw (.tcb b)).mpr ⟨b, rfl⟩
          rw [← h] at hy
          obtain ⟨_, hx, _⟩ := hr _ _ hy
          cases hx
        | _ => rfl

theorem of_runLinks {st' st : SystemState} (h : st'.objectsAgreeOffRunLinks st) :
    registersAgree st' st := fun t =>
  getTcb?_map_of_objects t KernelObject.withoutRunLinks
    (fun x => by cases x <;> simp [KernelObject.withoutRunLinks])
    (fun x y hx => by
      cases x <;> simp [KernelObject.withoutRunLinks] at hx
      exact ⟨_, rfl, by rw [← hx]; rfl⟩)
    (h t.toObjId)

theorem of_releaseLinks {st' st : SystemState} (h : st'.objectsAgreeOffReleaseLinks st) :
    registersAgree st' st := fun t =>
  getTcb?_map_of_objects t KernelObject.withoutRelease
    (fun x => by cases x <;> simp [KernelObject.withoutRelease])
    (fun x y hx => by
      cases x <;> simp [KernelObject.withoutRelease] at hx
      exact ⟨_, rfl, by rw [← hx]⟩)
    (h t.toObjId)

end registersAgree

/-- A context rewritten, then a thread updated keeping its registers, keeps
every register file. -/
theorem registersAgree.updateTcb_rewriteSchedContext (st : SystemState) (id : SeLe4n.ObjId)
    (sc' : SeLe4n.Kernel.SchedContext) (hA : st.rewriteAdmissible id (.schedContext sc'))
    (hInv : st.objects.invExt) (tid : SeLe4n.ThreadId) (f : TCB → TCB)
    (hf : ∀ t, (f t).registerContext = t.registerContext) :
    registersAgree ((st.rewriteObject id (.schedContext sc') hA).updateTcb tid f) st := by
  have hI1 := SystemState.rewriteObject_preserves_objects_invExt _ _ _ hA hInv
  intro t
  by_cases hE : tid.toObjId = t.toObjId
  · have : tid = t := SeLe4n.ThreadId.toObjId_injective _ _ hE
    subst this
    rw [SystemState.updateTcb_getTcb?_self _ _ _ hI1, Option.map_map,
      SystemState.rewriteObject_schedContext_getTcb? _ _ _ _ hInv]
    cases st.getTcb? tid with
    | none => rfl
    | some x => simp [hf]
  · rw [SystemState.updateTcb_getTcb?_ne _ _ _ hI1 _ hE,
      SystemState.rewriteObject_schedContext_getTcb? _ _ _ _ hInv]

/-- **The bind's writes keep every register file**: they are the context, the
thread's binding, the run-queue links and the release links. -/
theorem schedContextBindPerform_registersAgree (st : SystemState) (vS : SeLe4n.ValidObjId)
    (vT : SeLe4n.ValidThreadId) (hInv : st.objects.invExt) :
    registersAgree (SchedContextOps.schedContextBindPerform st vS vT) st := by
  unfold SchedContextOps.schedContextBindPerform
  split
  · exact registersAgree.refl _
  split
  · exact registersAgree.refl _
  refine registersAgree.trans
    (registersAgree.of_releaseLinks (SystemState.releasePlace_agree _ _ _)) ?_
  split
  · refine registersAgree.trans (fun t => by
      rw [SystemState.markReschedulePendingOnCore_getTcb?]) ?_
    refine registersAgree.trans
      (registersAgree.of_runLinks (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ _ _ _)) ?_
    exact registersAgree.updateTcb_rewriteSchedContext _ _ _ _ hInv _ _ (fun _ => rfl)
  · exact registersAgree.updateTcb_rewriteSchedContext _ _ _ _ hInv _ _ (fun _ => rfl)

/-- **The donation writes no thread's registers.** -/
theorem maybeDonateSchedContext_registersAgree (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    registersAgree (maybeDonateSchedContext st n tid) st :=
  maybeDonateSchedContext_induct (fun a b => registersAgree b a) st n tid
    (registersAgree.refl _) (fun vS vT _ _ => schedContextBindPerform_registersAgree st vS vT hInv)

/-- **The bind's perform writes the object store and the scheduler alone.** -/
theorem schedContextBindPerform_onlyObjectsSchedulerDiffer (st : SystemState)
    (vScId : SeLe4n.ValidObjId) (vTid : SeLe4n.ValidThreadId) :
    SystemState.onlyObjectsSchedulerDiffer (SchedContextOps.schedContextBindPerform st vScId vTid) st := by
  have hU : ∀ (s : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB),
      SystemState.onlyObjectsSchedulerDiffer (s.updateTcb t f) s := by
    intro s t f; unfold SystemState.updateTcb; split <;> rfl
  have hM : ∀ (s : SystemState) (c : Concurrency.CoreId),
      SystemState.onlyObjectsSchedulerDiffer (s.markReschedulePendingOnCore c) s := fun _ _ => rfl
  have hR : ∀ (s : SystemState) (k : SeLe4n.ObjId) (o : KernelObject) h,
      SystemState.onlyObjectsSchedulerDiffer (s.rewriteObject k o h) s := fun _ _ _ _ => rfl
  have hP : ∀ (s : SystemState) (c : Concurrency.CoreId) (x : SeLe4n.SchedContextId),
      SystemState.onlyObjectsSchedulerDiffer (s.releasePlace c x) s :=
    fun s c x => (SystemState.releasePlace_releaseOnlyWrite s c x).fields
  unfold SchedContextOps.schedContextBindPerform
  split
  · exact .refl st
  split
  · exact .refl st
  refine (hP _ _ _).trans ?_
  split
  · exact (hM _ _).trans ((SystemState.runEnqueueOnCore_onlyObjectsSchedulerDiffer _ _ _ _).trans
      ((hU _ _ _).trans (hR _ _ _ _)))
  · exact (hU _ _ _).trans (hR _ _ _ _)

/-- **A donation writes the object store and the scheduler alone**: the audit
trail, the machine and every other field are the state's. -/
theorem maybeDonateSchedContext_onlyObjectsSchedulerDiffer (st : SystemState) (n : SeLe4n.ObjId)
    (t : SeLe4n.ThreadId) :
    SystemState.onlyObjectsSchedulerDiffer (maybeDonateSchedContext st n t) st :=
  maybeDonateSchedContext_induct (fun a b => SystemState.onlyObjectsSchedulerDiffer b a) st n t
    (.refl st) (fun vS vT _ _ => schedContextBindPerform_onlyObjectsSchedulerDiffer st vS vT)
/-- A donation keeps the declassification audit trail. -/
theorem maybeDonateSchedContext_declassificationAuditLog_eq (st : SystemState) (n : SeLe4n.ObjId)
    (t : SeLe4n.ThreadId) :
    (maybeDonateSchedContext st n t).declassificationAuditLog = st.declassificationAuditLog := by
  have h := maybeDonateSchedContext_onlyObjectsSchedulerDiffer st n t
  unfold SystemState.onlyObjectsSchedulerDiffer at h
  rw [h]

end SeLe4n.Kernel
