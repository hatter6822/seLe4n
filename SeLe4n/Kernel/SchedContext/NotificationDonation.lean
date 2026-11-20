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
        simp only [hS, hT', ↓reduceDIte]
      have hT' : ¬ tid = SeLe4n.ThreadId.sentinel := hT
      simp only [hS, hT, ↓reduceDIte]
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

/-! ### seL4-MCS `maybeReturnSchedContext` -/

/-- **seL4-MCS `maybeReturnSchedContext`'s guard** (`notification.h`): the
context is the thread's own (`ntfn->ntfnSchedContext == tcb->tcbSchedContext`),
which seLe4n records as the thread's `.bound` binding naming it and the context
naming the thread back.  The back link is what seL4's pointer equality states of
a bound pair; under `schedContextBindingBidirectional` it follows from the first
conjunct, so this is seL4's guard on every reachable state. -/
@[inline] def schedContextReturnAdmitted (st : SystemState) (vS : SeLe4n.ValidObjId)
    (vT : SeLe4n.ValidThreadId) : Bool :=
  match st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val) with
  | none => false
  | some sc =>
    match st.getTcb? vT.val with
    | none => false
    | some tcb =>
      decide (sc.boundThread = some vT.val) &&
        decide (tcb.schedContextBinding = .bound (SeLe4n.SchedContextId.ofObjId vS.val))

/-- **seL4's return guard, as the footprints read it**: the notification is
bound to a context, the context names the thread and the thread holds it as its
own binding (`schedContextReturnAdmitted`). -/
def signalReturnGuard (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) : Bool :=
  match st.getNotification? n with
  | none => false
  | some ntfn =>
    match ntfn.schedContext with
    | none => false
    | some s =>
      match s.toObjId.toValid?, tid.toValid? with
      | some vS, some vT => schedContextReturnAdmitted st vS vT
      | _, _ => false

/-- seL4's return guard reads, of the context, the thread it names and, of the
thread, its binding. -/
theorem schedContextReturnAdmitted_eq_any (st : SystemState) (vS : SeLe4n.ValidObjId)
    (vT : SeLe4n.ValidThreadId) :
    schedContextReturnAdmitted st vS vT =
      (((st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val)).map
          (·.boundThread)).any (fun b => decide (b = some vT.val)) &&
        ((st.getTcb? vT.val).map (·.schedContextBinding)).any
          (fun b => decide (b = .bound (SeLe4n.SchedContextId.ofObjId vS.val)))) := by
  unfold schedContextReturnAdmitted
  cases st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val) <;>
    cases st.getTcb? vT.val <;> simp

/-- **The return guard reads three links**: the notification's context, the
context's thread and the thread's binding.  A step keeping all three keeps it. -/
theorem signalReturnGuard_congr {st st' : SystemState} {n : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId}
    (hN : (st'.getNotification? n).map (·.schedContext) =
      (st.getNotification? n).map (·.schedContext))
    (hS : ∀ s, (st'.getSchedContext? s).map (·.boundThread) =
      (st.getSchedContext? s).map (·.boundThread))
    (hT : (st'.getTcb? tid).map (·.schedContextBinding) =
      (st.getTcb? tid).map (·.schedContextBinding)) :
    signalReturnGuard st' n tid = signalReturnGuard st n tid := by
  unfold signalReturnGuard
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
            rw [schedContextReturnAdmitted_eq_any, schedContextReturnAdmitted_eq_any, hS,
              SeLe4n.ThreadId.toValid?_some_val_eq tid vT hTv, hT]

/-- **The cores a return writes the replenish queue of**: where the guard holds,
the purge's (`purgeReplenishCores`), the core the context's release link names. -/
def signalReturnReplenishCores (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) :
    List Concurrency.CoreId :=
  if signalReturnGuard st n tid then
    ((notificationContext? st n).map (SchedContextOps.purgeReplenishCores st)).getD []
  else []

/-- **The context a return writes**, where seL4's guard holds. -/
def signalReturnContext? (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) :
    Option SeLe4n.SchedContextId :=
  if signalReturnGuard st n tid then notificationContext? st n else none

/-- **Whether notification `n` holds a word**: a wait on it consumes the word
and completes (seL4's `completeSignal`, which donates), and a wait on a
notification holding none blocks (seL4's `receiveSignal`'s block, which returns
the context).  Read on a wait's entry state, it says which of the two the wait
runs, so a footprint locks the one it runs and not the other. -/
def notificationPending (st : SystemState) (n : SeLe4n.ObjId) : Bool :=
  match st.getNotification? n with
  | some ntfn => ntfn.pendingBadge.isSome
  | none => false

/-- **The context a wait's completion writes**, read on the wait's entry state:
the donation's where the notification holds a word, the return's where it holds
none. -/
def waitCompletionContext? (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) :
    Option SeLe4n.SchedContextId :=
  if notificationPending st n then signalDonationContext? st n tid
  else signalReturnContext? st n tid

/-! ### seL4-MCS `maybeReturnSchedContext`'s writes

seL4 runs one return, from two callers: `receiveIPC` (`endpoint.c`) on a
receiver that is still running, before it looks at the endpoint, and
`receiveSignal` (`notification.c`) on a waiter it has just blocked.  seL4's code
writes exactly three things: the thread's context pointer, the context's thread
pointer, and — the thread being the current one — `rescheduleRequired()`.  It
is not an unbind: it clears no current slot, dequeues nothing and leaves the
context's `isActive` and donation origin as they were.  So seLe4n's return is
those writes and the release-queue purge seLe4n's unbind runs
(`schedContextReturnPerform`), and both callers run it
(`maybeReturnSchedContext`).

**The purge is a model obligation, not a seL4 write.**  seLe4n's refill
invariant (`refillsSound`: `releaseQueuedBound`, every replenish-queue entry's
context is bound) has no counterpart in seL4, whose release queue holds threads.
A running receiver's context with a pending future refill sits on a replenish
queue; returning it by the three pointer writes alone would leave an unbound
context queued.  So the return, like seLe4n's unbind, takes the context off
whichever replenish queue holds it (`purgeReplenishment`, a no-op when it is on
none).  What a program sees is seL4's: an unbound context is never released in
seL4 either, and its refills, budget and `isActive` are left as they were. -/

/-- **seL4's three writes**: the context's thread link cleared, the thread's
binding cleared, and the core the thread is current on (`runningCoreOf?`)
flagged to reschedule (seL4's `rescheduleRequired()`).  The thread's current
slot, its queues and the context's budget and release link are untouched.  The
two flag hooks every binding writer runs (`markCandidacyGainFor`,
`markKeyChangeFor`) follow: they raise only reschedule flags, of the cores whose
queue or current slot holds the thread, so on a running receiver — current on
one core, queued on none — they flag at most the core already flagged. -/
@[inline] def schedContextReturnLinks (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getSchedContextWitnessed? (SeLe4n.SchedContextId.ofObjId vS.val) with
  | none => st
  | some ⟨sc, hSc⟩ =>
    match st.getTcb? tid with
    | none => st
    | some tcb =>
      let updatedSc := { sc with boundThreadCode := 0 }
      let st1 := st.rewriteObject vS.val (KernelObject.schedContext updatedSc)
        (SystemState.rewriteAdmissible_schedContext hSc updatedSc)
      let st2 := st1.updateTcb tid fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 }
      let st3 := match runningCoreOf? st tid with
        | some c => st2.markReschedulePendingOnCore c
        | none => st2
      markKeyChangeFor (markCandidacyGainFor st3 tid (hasSufficientBudget st tcb)) tid
        (effectiveSchedParams st tcb)

/-- **seL4's three writes, as compiled**: every word the flag hooks compare is
read before the first write, and the context and the thread are each rewritten
in their slot (`updateSchedContext`, `updateTcb`, whose compiled forms modify
the slot), so a kernel entry running the return builds no object. -/
@[inline] def schedContextReturnLinksImpl (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val) with
  | none => st
  | some _ =>
    match st.getTcb? tid with
    | none => st
    | some tcb =>
      let p := tcb.boostedPriority
      let d := tcb.deadline
      let dom := tcb.domain
      let e := hasSufficientBudget st tcb
      let rc := runningCoreOf? st tid
      let st1 := st.updateSchedContext (SeLe4n.SchedContextId.ofObjId vS.val)
        fun sc => { sc with boundThreadCode := 0 }
      let st2 := st1.updateTcb tid fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 }
      let st3 := match rc with
        | some c => st2.markReschedulePendingOnCore c
        | none => st2
      markKeyChangeParts (markCandidacyGainFor st3 tid e) tid p d dom

@[csimp] theorem schedContextReturnLinks_eq_impl :
    @schedContextReturnLinks = @schedContextReturnLinksImpl := by
  funext st vS tid
  unfold schedContextReturnLinks schedContextReturnLinksImpl
  split
  · next hW =>
    cases hS : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val) with
    | none => rfl
    | some sc => rw [SystemState.getSchedContextWitnessed?_eq_some hS] at hW; cases hW
  · next sc hS _ =>
    rw [hS]
    dsimp only
    cases st.getTcb? tid with
    | none => rfl
    | some tcb =>
      dsimp only
      rw [SystemState.updateSchedContext_eq_of_some hS, markKeyChangeFor_eq_parts]
      rfl

/-- **What seL4's return writes, object by object**: a slot keeps its object,
or holds a TCB whose two binding codes are cleared, or a context whose thread
link is cleared.  Every other field of every object — IPC states, queues,
budgets, notifications, endpoints — is the pre-state's. -/
theorem schedContextReturnLinks_objects (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (oid : SeLe4n.ObjId) :
    (schedContextReturnLinks st vS tid).objects[oid]? = st.objects[oid]? ∨
      (∃ tcb, st.objects[oid]? = some (.tcb tcb) ∧
        (schedContextReturnLinks st vS tid).objects[oid]? =
          some (.tcb { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 })) ∨
      (∃ sc, st.objects[oid]? = some (.schedContext sc) ∧
        (schedContextReturnLinks st vS tid).objects[oid]? =
          some (.schedContext { sc with boundThreadCode := 0 })) := by
  unfold schedContextReturnLinks
  split
  · exact Or.inl rfl
  rename_i sc hSc _
  split
  · exact Or.inl rfl
  rename_i tcb hT
  dsimp only
  have hFlag : ∀ (S : SystemState), (match runningCoreOf? st tid with
      | some c => S.markReschedulePendingOnCore c
      | none => S).objects = S.objects := fun S => by split <;> rfl
  rw [markKeyChangeFor_objects, markCandidacyGainFor_objects, hFlag,
    SystemState.updateTcb_after_rewriteObject_schedContext_objects st _ _ _ tid tcb _ hInv hT]
  have hScRaw := (SystemState.getSchedContext?_eq_some_iff st _ sc).mp hSc
  have hTRaw := (SystemState.getTcb?_eq_some_iff st _ tcb).mp hT
  have hInv1 := RobinHood.RHTable.insert_preserves_invExt st.objects vS.val
    (.schedContext { sc with boundThreadCode := 0 }) hInv
  simp only [RHTable_getElem?_eq_get?] at hScRaw hTRaw ⊢
  by_cases hT0 : tid.toObjId = oid
  · subst hT0
    exact Or.inr (Or.inl ⟨tcb, hTRaw, RobinHood.RHTable.getElem?_insert_self _ _ _ hInv1⟩)
  rw [RobinHood.RHTable.getElem?_insert_ne _ tid.toObjId oid _
    (by simp only [beq_iff_eq]; exact hT0) hInv1]
  by_cases hS0 : vS.val = oid
  · subst hS0
    exact Or.inr (Or.inr ⟨sc, hScRaw, RobinHood.RHTable.getElem?_insert_self _ _ _ hInv⟩)
  rw [RobinHood.RHTable.getElem?_insert_ne _ vS.val oid _
    (by simp only [beq_iff_eq]; exact hS0) hInv]
  exact Or.inl rfl

/-- **seL4's three writes store the context with its thread link cleared.** -/
theorem schedContextReturnLinks_getSchedContext?_self (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (sc : SchedContext) (tcb : TCB) (hInv : st.objects.invExt)
    (hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val) = some sc)
    (hT : st.getTcb? tid = some tcb) :
    (schedContextReturnLinks st vS tid).getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val) =
      some { sc with boundThreadCode := 0 } := by
  have key : ∀ (A B : SystemState), A.objects = B.objects → ∀ s,
      A.getSchedContext? s = B.getSchedContext? s := fun A B h s => by
    unfold SystemState.getSchedContext?; rw [h]
  unfold schedContextReturnLinks
  rw [SystemState.getSchedContextWitnessed?_eq_some hSc]
  dsimp only
  rw [hT]
  dsimp only
  have hInv1 := SystemState.rewriteObject_preserves_objects_invExt st vS.val
    (.schedContext { sc with boundThreadCode := 0 })
    (SystemState.rewriteAdmissible_schedContext hSc _) hInv
  refine (key _ (SystemState.updateTcb (st.rewriteObject vS.val
    (.schedContext { sc with boundThreadCode := 0 })
    (SystemState.rewriteAdmissible_schedContext hSc _)) tid
    fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 }) ?_ _).trans ?_
  · rw [markKeyChangeFor_objects, markCandidacyGainFor_objects]
    cases runningCoreOf? st tid <;> rfl
  · rw [SystemState.updateTcb_getSchedContext? _ _ _ hInv1]
    exact SystemState.rewriteObject_schedContext_getSchedContext?_self st _ _ _ hInv

/-- **seL4's three writes keep every release link**: they clear a context's
thread link and a TCB's binding codes, no release field. -/
theorem schedContextReturnLinks_releaseLinksAgree (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    SystemState.ReleaseLinksAgree (schedContextReturnLinks st vS tid) st := by
  intro c s
  rw [SystemState.releaseLinkOn_eq_obj, SystemState.releaseLinkOn_eq_obj]
  rcases schedContextReturnLinks_objects st vS tid hInv s.toObjId with e | ⟨y, hy, e⟩ | ⟨sc, hs, e⟩
  · rw [e]
  · rw [e, hy]; rfl
  · rw [e, hs]; rfl

/-- **seL4-MCS `maybeReturnSchedContext`'s writes, as seLe4n runs them**: seL4's three writes (`schedContextReturnLinks`), then the
context off whichever replenish queue holds it (`purgeReplenishment`, seLe4n's
unbind's purge; a no-op when it is queued nowhere).  The context's refills,
budget, `isActive` and donation origin are untouched, as in seL4. -/
@[inline] def schedContextReturnPerform (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) : SystemState :=
  SchedContextOps.purgeReplenishment (schedContextReturnLinks st vS tid)
    (SeLe4n.SchedContextId.ofObjId vS.val)

/-- **What the return writes, object by object**: a slot keeps its object, or
holds a TCB whose two binding codes are cleared, or holds a context in both
states (its thread link cleared, its release fields re-linked by the purge).
Every other field of every object — IPC states, queues, budgets,
notifications, endpoints — is the pre-state's. -/
theorem schedContextReturnPerform_objects (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (oid : SeLe4n.ObjId) :
    (schedContextReturnPerform st vS tid).objects[oid]? = st.objects[oid]? ∨
      (∃ tcb, st.objects[oid]? = some (.tcb tcb) ∧
        (schedContextReturnPerform st vS tid).objects[oid]? =
          some (.tcb { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 })) ∨
      (∃ sc sc', st.objects[oid]? = some (.schedContext sc) ∧
        (schedContextReturnPerform st vS tid).objects[oid]? = some (.schedContext sc')) := by
  have hA := SchedContextOps.purgeReplenishment_agree (schedContextReturnLinks st vS tid)
    (SeLe4n.SchedContextId.ofObjId vS.val)
  unfold schedContextReturnPerform
  rcases hA.pointwise oid with e | ⟨sc0, sc1, h0, h1, _⟩
  · rw [e]
    rcases schedContextReturnLinks_objects st vS tid hInv oid with e' | ⟨y, hy, e'⟩ | ⟨sc, hs, e'⟩
    · exact Or.inl e'
    · exact Or.inr (Or.inl ⟨y, hy, e'⟩)
    · exact Or.inr (Or.inr ⟨sc, _, hs, e'⟩)
  · rcases schedContextReturnLinks_objects st vS tid hInv oid with e' | ⟨y, hy, e'⟩ | ⟨sc, hs, _⟩
    · exact Or.inr (Or.inr ⟨sc0, sc1, by rw [← e']; exact h0, h1⟩)
    · rw [e'] at h0; cases h0
    · exact Or.inr (Or.inr ⟨sc, sc1, hs, h1⟩)

/-- **seL4's return keeps every TCB's IPC state** (and every field but the two
binding codes). -/
theorem schedContextReturnPerform_tcb (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (oid : SeLe4n.ObjId) (x : TCB)
    (h : (schedContextReturnPerform st vS tid).objects[oid]? = some (.tcb x)) :
    ∃ y, st.objects[oid]? = some (.tcb y) ∧
      (x = y ∨ x = { y with scBindingScCode := 0, scBindingOwnerCode := 0 }) := by
  rcases schedContextReturnPerform_objects st vS tid hInv oid with e | ⟨y, hy, e⟩ | ⟨sc, sc', _, e⟩
  · rw [e] at h; exact ⟨x, h, Or.inl rfl⟩
  · rw [e] at h; cases h; exact ⟨y, hy, Or.inr rfl⟩
  · rw [e] at h; cases h

/-- **seL4's return keeps every object that is neither a TCB nor a context.** -/
theorem schedContextReturnPerform_other (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (oid : SeLe4n.ObjId)
    (hNT : ∀ t, st.objects[oid]? ≠ some (.tcb t))
    (hNS : ∀ sc, st.objects[oid]? ≠ some (.schedContext sc)) :
    (schedContextReturnPerform st vS tid).objects[oid]? = st.objects[oid]? := by
  rcases schedContextReturnPerform_objects st vS tid hInv oid with e | ⟨y, hy, _⟩ | ⟨sc, _, hs, _⟩
  · exact e
  · exact absurd hy (hNT y)
  · exact absurd hs (hNS sc)

/-- **seL4-MCS `maybeReturnSchedContext`**: seL4's guard
(`schedContextReturnAdmitted`), then seL4's writes and the purge
(`schedContextReturnPerform`); else the state unchanged, as seL4 does nothing.
The notification keeps its link to the context.  The blocking `Wait`'s return
and the receive's (`receiveReturnSchedContext`) are this one operation. -/
def maybeReturnSchedContext (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getNotification? n with
  | none => st
  | some ntfn =>
    match ntfn.schedContext with
    | none => st
    | some s =>
      match s.toObjId.toValid?, tid.toValid? with
      | some vS, some vT =>
        if schedContextReturnAdmitted st vS vT then schedContextReturnPerform st vS tid
        else st
      | _, _ => st

/-- **The return is the identity or seL4's writes under seL4's guard.** -/
theorem maybeReturnSchedContext_cases (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) :
    maybeReturnSchedContext st n tid = st ∨
      ∃ (vS : SeLe4n.ValidObjId) (vT : SeLe4n.ValidThreadId), vT.val = tid ∧
        (∃ ntfn s, st.getNotification? n = some ntfn ∧ ntfn.schedContext = some s ∧
          s.toObjId = vS.val) ∧
        schedContextReturnAdmitted st vS vT = true ∧
        maybeReturnSchedContext st n tid = schedContextReturnPerform st vS tid := by
  unfold maybeReturnSchedContext
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

/-- **A property the identity and seL4's writes under the guard carry, the
return carries.** -/
theorem maybeReturnSchedContext_induct (P : SystemState → SystemState → Prop)
    (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (hId : P st st)
    (hRet : ∀ (vS : SeLe4n.ValidObjId) (vT : SeLe4n.ValidThreadId), vT.val = tid →
      schedContextReturnAdmitted st vS vT = true → P st (schedContextReturnPerform st vS tid)) :
    P st (maybeReturnSchedContext st n tid) := by
  rcases maybeReturnSchedContext_cases st n tid with h | ⟨vS, vT, hT, _, hA, h⟩
  · rw [h]; exact hId
  · rw [h]; exact hRet vS vT hT hA

/-- **Where the guard fails the return writes nothing.** -/
theorem maybeReturnSchedContext_of_guard_false {st : SystemState} {n : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} (h : signalReturnGuard st n tid = false) :
    maybeReturnSchedContext st n tid = st := by
  unfold signalReturnGuard at h
  unfold maybeReturnSchedContext
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

/-- **The compiled return**, the ids passed as their codes: seL4's
guard asked before any write, then seL4's three writes in place.  A context code
at or past `2 ^ 62` — which no object store holds — takes the specification. -/
@[noinline] def maybeReturnSchedContextFast (st : SystemState) (nCode tCode : Nat) :
    SystemState :=
  match st.getNotification? ⟨nCode⟩ with
  | none => st
  | some ntfn =>
    let sCode := ntfn.schedContextCode
    if sCode = 0 then st
    else if sCode < 2 ^ 62 then
      if hS : (⟨sCode - 1⟩ : SeLe4n.ObjId) = SeLe4n.ObjId.sentinel then st
      else if hT : (⟨tCode⟩ : SeLe4n.ThreadId) = SeLe4n.ThreadId.sentinel then st
      else if schedContextReturnAdmitted st ⟨⟨sCode - 1⟩, hS⟩ ⟨⟨tCode⟩, hT⟩ then
        schedContextReturnPerform st ⟨⟨sCode - 1⟩, hS⟩ ⟨tCode⟩
      else st
    else maybeReturnSchedContext st ⟨nCode⟩ ⟨tCode⟩

/-- **The compiled return is the return.** -/
theorem maybeReturnSchedContextFast_eq (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) :
    maybeReturnSchedContextFast st n.val tid.val = maybeReturnSchedContext st n tid := by
  unfold maybeReturnSchedContextFast
  cases hN : st.getNotification? ⟨n.val⟩ with
  | none =>
    unfold maybeReturnSchedContext
    rw [show (⟨n.val⟩ : SeLe4n.ObjId) = n from rfl] at hN
    rw [hN]
  | some ntfn =>
    have hN' : st.getNotification? n = some ntfn := hN
    simp only
    by_cases h0 : ntfn.schedContextCode = 0
    · unfold maybeReturnSchedContext
      simp only [h0, ↓reduceIte, hN', Notification.schedContext, SeLe4n.SchedContextId.ofOptCode]
    by_cases hW : ntfn.schedContextCode < 2 ^ 62
    · simp only [h0, hW, ↓reduceIte]
      unfold maybeReturnSchedContext
      obtain ⟨k, hk⟩ : ∃ k, ntfn.schedContextCode = k + 1 :=
        ⟨ntfn.schedContextCode - 1, by omega⟩
      simp only [hN', Notification.schedContext, hk, SeLe4n.SchedContextId.ofOptCode, Nat.add_sub_cancel,
        SeLe4n.SchedContextId.toObjId, SeLe4n.SchedContextId.toNat, SeLe4n.ObjId.ofNat,
        SeLe4n.ObjId.toValid?, SeLe4n.ThreadId.toValid?]
      by_cases hS : (⟨k⟩ : SeLe4n.ObjId) = SeLe4n.ObjId.sentinel
      · simp only [hS, ↓reduceDIte]
      by_cases hT : (⟨tid.val⟩ : SeLe4n.ThreadId) = SeLe4n.ThreadId.sentinel
      · have hT' : tid = SeLe4n.ThreadId.sentinel := hT
        simp only [hS, hT', ↓reduceDIte]
      have hT' : ¬ tid = SeLe4n.ThreadId.sentinel := hT
      simp only [hS, hT, ↓reduceDIte]
    · simp only [h0, hW, ↓reduceIte]

/-- **seL4 `receiveIPC`'s return, as the receive runs it**: a blocking receive
by a thread with a bound notification returns that notification's context
(`maybeReturnSchedContext`) when the receive did not complete the
notification; a non-blocking receive, or a thread with no bound notification,
writes nothing. -/
def receiveReturnSchedContext (blocks : Bool) (st : SystemState) (tid : SeLe4n.ThreadId) :
    SystemState :=
  if blocks then
    match st.getTcb? tid with
    | some t =>
      if t.boundNotificationCode = 0 then st
      else maybeReturnSchedContext st ⟨t.boundNotificationCode - 1⟩ tid
    | none => st
  else st

/-- **A property the identity and seL4's writes carry, the receive's return
carries.** -/
theorem receiveReturnSchedContext_induct (P : SystemState → SystemState → Prop)
    (blocks : Bool) (st : SystemState) (tid : SeLe4n.ThreadId)
    (hId : P st st)
    (hRet : ∀ (vS : SeLe4n.ValidObjId) (vT : SeLe4n.ValidThreadId), vT.val = tid →
      schedContextReturnAdmitted st vS vT = true → P st (schedContextReturnPerform st vS tid)) :
    P st (receiveReturnSchedContext blocks st tid) := by
  unfold receiveReturnSchedContext
  split
  · split
    · split
      · exact hId
      · exact maybeReturnSchedContext_induct P st _ tid hId hRet
    · exact hId
  · exact hId

/-- **The receive's return keeps every TCB but for its two binding codes.** -/
theorem receiveReturnSchedContext_tcb (blocks : Bool) (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (oid : SeLe4n.ObjId) (x : TCB)
    (h : (receiveReturnSchedContext blocks st tid).objects[oid]? = some (.tcb x)) :
    ∃ y, st.objects[oid]? = some (.tcb y) ∧
      (x = y ∨ x = { y with scBindingScCode := 0, scBindingOwnerCode := 0 }) :=
  receiveReturnSchedContext_induct (fun a b => ∀ x, b.objects[oid]? = some (.tcb x) →
      ∃ y, a.objects[oid]? = some (.tcb y) ∧
        (x = y ∨ x = { y with scBindingScCode := 0, scBindingOwnerCode := 0 }))
    blocks st tid (fun x h => ⟨x, h, Or.inl rfl⟩)
    (fun vS _ _ _ => schedContextReturnPerform_tcb st vS tid hInv oid) x h

/-- **The receive's return keeps every object that is neither a TCB nor a
context.** -/
theorem receiveReturnSchedContext_other (blocks : Bool) (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (oid : SeLe4n.ObjId)
    (hNT : ∀ t, st.objects[oid]? ≠ some (.tcb t))
    (hNS : ∀ sc, st.objects[oid]? ≠ some (.schedContext sc)) :
    (receiveReturnSchedContext blocks st tid).objects[oid]? = st.objects[oid]? :=
  receiveReturnSchedContext_induct (fun a b => b.objects[oid]? = a.objects[oid]?)
    blocks st tid rfl (fun vS _ _ _ => schedContextReturnPerform_other st vS tid hInv oid hNT hNS)

/-- **The receive's return keeps every slot's kind**: a slot holds an object
after it exactly when it did before, and of the same kind. -/
theorem receiveReturnSchedContext_objects (blocks : Bool) (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (oid : SeLe4n.ObjId) :
    (receiveReturnSchedContext blocks st tid).objects[oid]? = st.objects[oid]? ∨
      (∃ tcb, st.objects[oid]? = some (.tcb tcb) ∧
        (receiveReturnSchedContext blocks st tid).objects[oid]? =
          some (.tcb { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 })) ∨
      (∃ sc sc', st.objects[oid]? = some (.schedContext sc) ∧
        (receiveReturnSchedContext blocks st tid).objects[oid]? = some (.schedContext sc')) :=
  receiveReturnSchedContext_induct (fun a b => b.objects[oid]? = a.objects[oid]? ∨
      (∃ tcb, a.objects[oid]? = some (.tcb tcb) ∧
        b.objects[oid]? = some (.tcb { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 })) ∨
      (∃ sc sc', a.objects[oid]? = some (.schedContext sc) ∧
        b.objects[oid]? = some (.schedContext sc')))
    blocks st tid (Or.inl rfl) (fun vS _ _ _ => schedContextReturnPerform_objects st vS tid hInv oid)

/-- **seL4's return on a running receiver keeps the object store's integrity.** -/
theorem schedContextReturnLinks_preserves_objects_invExt (st : SystemState)
    (vS : SeLe4n.ValidObjId) (tid : SeLe4n.ThreadId) (hObjInv : st.objects.invExt) :
    (schedContextReturnLinks st vS tid).objects.invExt := by
  unfold schedContextReturnLinks
  split
  · exact hObjInv
  split
  · exact hObjInv
  dsimp only
  have hFlag : ∀ (S : SystemState), (match runningCoreOf? st tid with
      | some c => S.markReschedulePendingOnCore c
      | none => S).objects = S.objects := fun S => by split <;> rfl
  rw [markKeyChangeFor_objects, markCandidacyGainFor_objects, hFlag]
  exact SystemState.updateTcb_preserves_objects_invExt _ tid _
    (SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hObjInv)

/-- **The return keeps the object store's integrity**: seL4's three writes,
then the purge. -/
theorem schedContextReturnPerform_preserves_objects_invExt (st : SystemState)
    (vS : SeLe4n.ValidObjId) (tid : SeLe4n.ThreadId) (hObjInv : st.objects.invExt) :
    (schedContextReturnPerform st vS tid).objects.invExt :=
  SchedContextOps.purgeReplenishment_objects_invExt _ _
    (schedContextReturnLinks_preserves_objects_invExt st vS tid hObjInv)

/-- **The receive's return keeps the object store's integrity.** -/
theorem receiveReturnSchedContext_objects_invExt (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (hObjInv : st.objects.invExt) :
    (receiveReturnSchedContext blocks st tid).objects.invExt :=
  receiveReturnSchedContext_induct (fun _ b => b.objects.invExt) blocks st tid hObjInv
    (fun vS _ _ _ => schedContextReturnPerform_preserves_objects_invExt st vS tid hObjInv)

/-- **Whether the receive's return writes**: a blocking receive by a thread
whose bound notification's context is its own (`signalReturnGuard`). -/
@[inline] def receiveReturnFires (blocks : Bool) (st : SystemState) (tid : SeLe4n.ThreadId) :
    Bool :=
  blocks &&
    (match st.getTcb? tid with
     | some t => t.boundNotificationCode != 0 &&
         signalReturnGuard st ⟨t.boundNotificationCode - 1⟩ tid
     | none => false)

/-- **Where it does not fire the receive's return writes nothing.** -/
theorem receiveReturnSchedContext_of_fires_false {blocks : Bool} {st : SystemState}
    {tid : SeLe4n.ThreadId} (h : receiveReturnFires blocks st tid = false) :
    receiveReturnSchedContext blocks st tid = st := by
  unfold receiveReturnFires at h
  unfold receiveReturnSchedContext
  cases blocks with
  | false => rfl
  | true =>
    simp only [Bool.true_and] at h
    simp only [↓reduceIte]
    cases hT : st.getTcb? tid with
    | none => rfl
    | some t =>
      rw [hT] at h
      simp only at h ⊢
      by_cases h0 : t.boundNotificationCode = 0
      · simp only [h0, ↓reduceIte]
      · simp only [h0, ↓reduceIte]
        have hG : signalReturnGuard st ⟨t.boundNotificationCode - 1⟩ tid = false := by
          simpa [h0] using h
        exact maybeReturnSchedContext_of_guard_false hG


/-- **Every TCB the receive's return was handed is still there**, its binding
codes cleared or not. -/
theorem receiveReturnSchedContext_tcb_fwd (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (oid : SeLe4n.ObjId) (y : TCB)
    (h : st.objects[oid]? = some (.tcb y)) :
    ∃ x, (receiveReturnSchedContext blocks st tid).objects[oid]? = some (.tcb x) ∧
      (x = y ∨ x = { y with scBindingScCode := 0, scBindingOwnerCode := 0 }) := by
  rcases receiveReturnSchedContext_objects blocks st tid hInv oid with e | ⟨y', hy, e⟩ | ⟨_, _, hs, _⟩
  · exact ⟨y, by rw [e]; exact h, Or.inl rfl⟩
  · rw [h] at hy; cases hy; exact ⟨_, e, Or.inr rfl⟩
  · rw [h] at hs; cases hs

/-- **seL4's return keeps every core's current slot**: it raises flags only. -/
theorem schedContextReturnLinks_currentOnCore (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (c : Concurrency.CoreId) :
    (schedContextReturnLinks st vS tid).scheduler.currentOnCore c =
      st.scheduler.currentOnCore c := by
  unfold schedContextReturnLinks
  split
  · rfl
  split
  · rfl
  dsimp only
  rw [markKeyChangeFor_extract_frame (fun s => s.scheduler.currentOnCore c) _ _ _
      (fun _ _ => by simp [SystemState.markReschedulePendingOnCore]),
    markCandidacyGainFor_extract_frame (fun s => s.scheduler.currentOnCore c) _ _ _
      (fun _ _ => by simp [SystemState.markReschedulePendingOnCore])]
  split <;> simp [SystemState.markReschedulePendingOnCore, SystemState.updateTcb_scheduler,
    SystemState.rewriteObject_scheduler]

/-- **The return keeps every core's current slot**: the purge writes release
links and replenish queues only. -/
theorem schedContextReturnPerform_currentOnCore (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (c : Concurrency.CoreId) :
    (schedContextReturnPerform st vS tid).scheduler.currentOnCore c =
      st.scheduler.currentOnCore c := by
  unfold schedContextReturnPerform
  rw [SchedContextOps.purgeReplenishment_currentOnCore, schedContextReturnLinks_currentOnCore]

/-- **The receive's return keeps every core's current slot.** -/
theorem receiveReturnSchedContext_currentOnCore (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : Concurrency.CoreId) :
    (receiveReturnSchedContext blocks st tid).scheduler.currentOnCore c =
      st.scheduler.currentOnCore c :=
  receiveReturnSchedContext_induct
    (fun a b => b.scheduler.currentOnCore c = a.scheduler.currentOnCore c) blocks st tid rfl
    (fun vS _ _ _ => schedContextReturnPerform_currentOnCore st vS tid c)

/-- **The syscall word the caller trapped with**: its saved `x7`
(`arm64DefaultLayout.syscallNumReg`); `0`, which names no syscall, for a
caller with no TCB.  Stated here, beside the receive's return, because the
receive's lock sets read it to resolve whether the receive blocks
(`receiveLegState`). -/
@[inline] def callerSyscallWord (st : SystemState) (tid : SeLe4n.ThreadId) : UInt64 :=
  match st.getTcb? tid with
  | some t => SeLe4n.readRegWord t.registerContext SeLe4n.arm64DefaultLayout.syscallNumReg
  | none => 0

/-- **The state a receive's endpoint leg runs on**: seL4-MCS `receiveIPC`'s
`maybeReturnSchedContext`, for a blocking receive, applied to the state the leg
is handed.  One owner for the dispatch and for the footprints that re-run the
leg. -/
def receiveLegState (st : SystemState) (receiver : SeLe4n.ThreadId) : SystemState :=
  receiveReturnSchedContext (Syscall.wordReceiveBlocks (callerSyscallWord st receiver)) st receiver

/-- **The context a blocking receive returns**, read on the state the return
runs on: the bound notification's context where the receive blocks and seL4's
guard holds (`receiveReturnFires`), `none` otherwise. -/
def receiveReturnContextAt? (blocks : Bool) (st : SystemState) (receiver : SeLe4n.ThreadId) :
    Option SeLe4n.SchedContextId :=
  if blocks then
    match st.getTcb? receiver with
    | some t => if t.boundNotificationCode = 0 then none
        else signalReturnContext? st ⟨t.boundNotificationCode - 1⟩ receiver
    | none => none
  else none

/-- The context the `.receive` arm's return returns: `receiveReturnContextAt?`
at the blocking flag of the caller's syscall word. -/
def receiveReturnContext? (st : SystemState) (receiver : SeLe4n.ThreadId) :
    Option SeLe4n.SchedContextId :=
  receiveReturnContextAt? (Syscall.wordReceiveBlocks (callerSyscallWord st receiver)) st receiver

/-- **The notification context a blocking receive may return**: its bound
notification's context where the receive blocks, read without seL4's guard —
the guard's superset, which a footprint locks where an earlier step of the same
syscall (the busy-reply cancel) may change what the guard reads. -/
def receiveReturnNotificationContext? (st : SystemState) (receiver : SeLe4n.ThreadId) :
    Option SeLe4n.SchedContextId :=
  if Syscall.wordReceiveBlocks (callerSyscallWord st receiver) then
    match st.getTcb? receiver with
    | some t => if t.boundNotificationCode = 0 then none
        else notificationContext? st ⟨t.boundNotificationCode - 1⟩
    | none => none
  else none

/-- The context a return writes is the notification context it may return. -/
theorem receiveReturnNotificationContext?_of_receiveReturnContext? {st : SystemState}
    {receiver : SeLe4n.ThreadId} {s : SeLe4n.SchedContextId}
    (h : receiveReturnContext? st receiver = some s) :
    receiveReturnNotificationContext? st receiver = some s := by
  unfold receiveReturnContext? receiveReturnContextAt? at h
  unfold receiveReturnNotificationContext?
  split at h
  · rename_i hB
    simp only [hB, ↓reduceIte]
    split at h
    · split at h
      · cases h
      · rename_i h0
        simp only [h0, ↓reduceIte]
        unfold signalReturnContext? at h
        split at h
        · exact h
        · cases h
    · cases h
  · cases h

/-- **The return writes no scheduler field but a reschedule flag**: any
projection of the scheduler that the flag write leaves alone, the return leaves
alone. -/
theorem schedContextReturnLinks_scheduler_frame {F : Type} (f : SchedulerState → F)
    (st : SystemState) (vS : SeLe4n.ValidObjId) (tid : SeLe4n.ThreadId)
    (h : ∀ (s : SystemState) c, f (s.markReschedulePendingOnCore c).scheduler = f s.scheduler) :
    f (schedContextReturnLinks st vS tid).scheduler = f st.scheduler := by
  unfold schedContextReturnLinks
  split
  · rfl
  split
  · rfl
  dsimp only
  rw [markKeyChangeFor_extract_frame (fun s => f s.scheduler) _ _ _ h,
    markCandidacyGainFor_extract_frame (fun s => f s.scheduler) _ _ _ h]
  split
  · rw [h]; simp only [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]
  · simp only [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]

/-- **The return writes no scheduler field but a reschedule flag and the purged
replenish queue**: any projection of the scheduler that the flag write and the
purge leave alone, the return leaves alone. -/
theorem schedContextReturnPerform_scheduler_frame {F : Type} (f : SchedulerState → F)
    (st : SystemState) (vS : SeLe4n.ValidObjId) (tid : SeLe4n.ThreadId)
    (h : ∀ (s : SystemState) c, f (s.markReschedulePendingOnCore c).scheduler = f s.scheduler)
    (hP : ∀ (s : SystemState) x, f (SchedContextOps.purgeReplenishment s x).scheduler =
      f s.scheduler) :
    f (schedContextReturnPerform st vS tid).scheduler = f st.scheduler := by
  unfold schedContextReturnPerform
  rw [hP, schedContextReturnLinks_scheduler_frame f st vS tid h]

/-- **The return moves the replenish queue of the purge's core and no other**:
the core the context's own release link names on the pre-state
(`purgeReplenishCores`); seL4's three writes keep every release link. -/
theorem schedContextReturnPerform_replenishQueueOnCore_ne (st : SystemState)
    (vS : SeLe4n.ValidObjId) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (d : Concurrency.CoreId)
    (h : d ∉ SchedContextOps.purgeReplenishCores st (SeLe4n.SchedContextId.ofObjId vS.val)) :
    (schedContextReturnPerform st vS tid).scheduler.replenishQueueOnCore d =
      st.scheduler.replenishQueueOnCore d := by
  unfold schedContextReturnPerform
  rw [SchedContextOps.purgeReplenishment_replenishQueueOnCore_ne _ _ _ ?_]
  · exact schedContextReturnLinks_scheduler_frame (fun s => s.replenishQueueOnCore d) st vS tid
      (fun _ _ => by simp [SystemState.markReschedulePendingOnCore])
  · rw [SystemState.releaseCoreOf_of_linksAgree
      (schedContextReturnLinks_releaseLinksAgree st vS tid hInv)]
    intro hc
    apply h
    unfold SchedContextOps.purgeReplenishCores
    rw [hc]
    exact List.mem_singleton_self d

/-- ...and so does the receive's return. -/
theorem receiveReturnSchedContext_scheduler_frame {F : Type} (f : SchedulerState → F)
    (blocks : Bool) (st : SystemState) (tid : SeLe4n.ThreadId)
    (h : ∀ (s : SystemState) c, f (s.markReschedulePendingOnCore c).scheduler = f s.scheduler)
    (hP : ∀ (s : SystemState) x, f (SchedContextOps.purgeReplenishment s x).scheduler =
      f s.scheduler) :
    f (receiveReturnSchedContext blocks st tid).scheduler = f st.scheduler :=
  receiveReturnSchedContext_induct (fun a b => f b.scheduler = f a.scheduler) blocks st tid rfl
    (fun vS _ _ _ => schedContextReturnPerform_scheduler_frame f st vS tid h hP)

/-- **The receive's return moves no run queue or active domain.** -/
theorem receiveReturnSchedContext_queues (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (d : Concurrency.CoreId) :
    (receiveReturnSchedContext blocks st tid).scheduler.runQueueOnCore d =
        st.scheduler.runQueueOnCore d ∧
      (receiveReturnSchedContext blocks st tid).scheduler.activeDomainOnCore d =
        st.scheduler.activeDomainOnCore d :=
  ⟨receiveReturnSchedContext_scheduler_frame (fun s => s.runQueueOnCore d) blocks st tid
      (fun _ _ => by simp [SystemState.markReschedulePendingOnCore])
      (fun _ _ => SchedContextOps.purgeReplenishment_runQueueOnCore _ _ _),
    receiveReturnSchedContext_scheduler_frame (fun s => s.activeDomainOnCore d) blocks st tid
      (fun _ _ => by simp [SystemState.markReschedulePendingOnCore])
      (fun _ _ => SchedContextOps.purgeReplenishment_activeDomainOnCore _ _ _)⟩

/-- **The return keeps every slot's kind**: a slot holds an object after it
exactly when it did before, and of the same kind. -/
theorem maybeReturnSchedContext_objects (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (oid : SeLe4n.ObjId) :
    (maybeReturnSchedContext st n tid).objects[oid]? = st.objects[oid]? ∨
      (∃ tcb, st.objects[oid]? = some (.tcb tcb) ∧
        (maybeReturnSchedContext st n tid).objects[oid]? =
          some (.tcb { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 })) ∨
      (∃ sc sc', st.objects[oid]? = some (.schedContext sc) ∧
        (maybeReturnSchedContext st n tid).objects[oid]? = some (.schedContext sc')) :=
  maybeReturnSchedContext_induct (fun a b => b.objects[oid]? = a.objects[oid]? ∨
      (∃ tcb, a.objects[oid]? = some (.tcb tcb) ∧
        b.objects[oid]? = some (.tcb { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 })) ∨
      (∃ sc sc', a.objects[oid]? = some (.schedContext sc) ∧
        b.objects[oid]? = some (.schedContext sc')))
    st n tid (Or.inl rfl) (fun vS _ _ _ => schedContextReturnPerform_objects st vS tid hInv oid)

/-- **The return keeps the object store's integrity.** -/
theorem maybeReturnSchedContext_objects_invExt (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (hObjInv : st.objects.invExt) :
    (maybeReturnSchedContext st n tid).objects.invExt :=
  maybeReturnSchedContext_induct (fun _ b => b.objects.invExt) st n tid hObjInv
    (fun vS _ _ _ => schedContextReturnPerform_preserves_objects_invExt st vS tid hObjInv)

/-- **The return writes no scheduler field but a reschedule flag and the purged
replenish queue.** -/
theorem maybeReturnSchedContext_scheduler_frame {F : Type} (f : SchedulerState → F)
    (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (h : ∀ (s : SystemState) c, f (s.markReschedulePendingOnCore c).scheduler = f s.scheduler)
    (hP : ∀ (s : SystemState) x, f (SchedContextOps.purgeReplenishment s x).scheduler =
      f s.scheduler) :
    f (maybeReturnSchedContext st n tid).scheduler = f st.scheduler :=
  maybeReturnSchedContext_induct (fun a b => f b.scheduler = f a.scheduler) st n tid rfl
    (fun vS _ _ _ => schedContextReturnPerform_scheduler_frame f st vS tid h hP)

/-- **The return moves no run queue, current slot or active domain**: seL4's
`maybeReturnSchedContext` dequeues nothing and leaves the thread where it is
(`rescheduleRequired()` is a flag). -/
theorem maybeReturnSchedContext_runSlots (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (d : Concurrency.CoreId) :
    (maybeReturnSchedContext st n tid).scheduler.runQueueOnCore d =
        st.scheduler.runQueueOnCore d ∧
      (maybeReturnSchedContext st n tid).scheduler.currentOnCore d =
        st.scheduler.currentOnCore d ∧
      (maybeReturnSchedContext st n tid).scheduler.activeDomainOnCore d =
        st.scheduler.activeDomainOnCore d :=
  ⟨maybeReturnSchedContext_scheduler_frame (fun s => s.runQueueOnCore d) st n tid
      (fun _ _ => by simp [SystemState.markReschedulePendingOnCore])
      (fun _ _ => SchedContextOps.purgeReplenishment_runQueueOnCore _ _ _),
    maybeReturnSchedContext_induct
      (fun a b => b.scheduler.currentOnCore d = a.scheduler.currentOnCore d) st n tid rfl
      (fun vS _ _ _ => schedContextReturnPerform_currentOnCore st vS tid d),
    maybeReturnSchedContext_scheduler_frame (fun s => s.activeDomainOnCore d) st n tid
      (fun _ _ => by simp [SystemState.markReschedulePendingOnCore])
      (fun _ _ => SchedContextOps.purgeReplenishment_activeDomainOnCore _ _ _)⟩

/-- **The cores whose replenish queue a receive's return writes**: the purge's
core (`purgeReplenishCores`) of the context it returns
(`receiveReturnContext?`), read on the state the return runs on; none where the
return does not fire. -/
def receiveReturnReplenishCoresAt (blocks : Bool) (st : SystemState)
    (receiver : SeLe4n.ThreadId) : List Concurrency.CoreId :=
  ((receiveReturnContextAt? blocks st receiver).map (SchedContextOps.purgeReplenishCores st)).getD []

/-- The `.receive` arm's: `receiveReturnReplenishCoresAt` at the blocking flag of
the caller's syscall word. -/
def receiveReturnReplenishCores (st : SystemState) (receiver : SeLe4n.ThreadId) :
    List Concurrency.CoreId :=
  receiveReturnReplenishCoresAt (Syscall.wordReceiveBlocks (callerSyscallWord st receiver)) st
    receiver

/-- **The return moves the replenish queue of the returned context's
purge core and no other.** -/
theorem maybeReturnSchedContext_replenishQueueOnCore_ne (st : SystemState)
    (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (d : Concurrency.CoreId)
    (h : d ∉ ((signalReturnContext? st n tid).map (SchedContextOps.purgeReplenishCores st)).getD []) :
    (maybeReturnSchedContext st n tid).scheduler.replenishQueueOnCore d =
      st.scheduler.replenishQueueOnCore d := by
  unfold signalReturnContext? signalReturnGuard notificationContext? at h
  unfold maybeReturnSchedContext
  cases hN : st.getNotification? n with
  | none => rfl
  | some ntfn =>
    rw [hN] at h
    dsimp only
    cases hS : ntfn.schedContext with
    | none => rfl
    | some s =>
      simp only [hS, Option.bind_some] at h ⊢
      cases hV : s.toObjId.toValid? with
      | none => rfl
      | some vS =>
        cases hT : tid.toValid? with
        | none => simp only
        | some vT =>
          simp only [hV, hT] at h ⊢
          by_cases hA : schedContextReturnAdmitted st vS vT = true
          · simp only [hA, ↓reduceIte, Option.map_some, Option.getD_some] at h ⊢
            have hsv : SeLe4n.SchedContextId.ofObjId vS.val = s := by
              unfold SeLe4n.ObjId.toValid? at hV
              split at hV
              · cases hV
              · cases hV; rfl
            exact schedContextReturnPerform_replenishQueueOnCore_ne st vS tid hInv d (by rw [hsv]; exact h)
          · simp only [hA, Bool.false_eq_true, ↓reduceIte]

/-- **The purge's cores of the context the return writes are the return's
replenish cores** (`signalReturnReplenishCores`). -/
theorem signalReturnContext?_purgeCores (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) :
    ((signalReturnContext? st n tid).map (SchedContextOps.purgeReplenishCores st)).getD [] =
      signalReturnReplenishCores st n tid := by
  unfold signalReturnContext? signalReturnReplenishCores
  split <;> rfl

/-- The leg's state keeps the object-store invariant. -/
theorem receiveLegState_objects_invExt (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) : (receiveLegState st receiver).objects.invExt :=
  receiveReturnSchedContext_objects_invExt _ st receiver hObjInv

/-- The leg's state has every queue, current slot and active domain of the
state it is read from. -/
theorem receiveLegState_queues (st : SystemState) (receiver : SeLe4n.ThreadId)
    (d : Concurrency.CoreId) :
    (receiveLegState st receiver).scheduler.runQueueOnCore d = st.scheduler.runQueueOnCore d ∧
      (receiveLegState st receiver).scheduler.activeDomainOnCore d =
        st.scheduler.activeDomainOnCore d ∧
      (receiveLegState st receiver).scheduler.currentOnCore d = st.scheduler.currentOnCore d :=
  let h := receiveReturnSchedContext_queues
    (Syscall.wordReceiveBlocks (callerSyscallWord st receiver)) st receiver d
  ⟨h.1, h.2, receiveReturnSchedContext_currentOnCore _ st receiver d⟩

/-- **The receive's return moves the replenish queue of the returned context's
purge core and no other** (`receiveReturnReplenishCoresAt`). -/
theorem receiveReturnSchedContext_replenishQueueOnCore_ne (blocks : Bool) (st : SystemState)
    (receiver : SeLe4n.ThreadId) (hInv : st.objects.invExt) (d : Concurrency.CoreId)
    (h : d ∉ receiveReturnReplenishCoresAt blocks st receiver) :
    (receiveReturnSchedContext blocks st receiver).scheduler.replenishQueueOnCore d =
      st.scheduler.replenishQueueOnCore d := by
  unfold receiveReturnReplenishCoresAt receiveReturnContextAt? at h
  unfold receiveReturnSchedContext
  split
  · rename_i hB
    simp only [hB, ↓reduceIte] at h
    split
    · rename_i t hT
      rw [hT] at h
      split
      · rfl
      · rename_i h0
        simp only [h0, ↓reduceIte] at h
        exact maybeReturnSchedContext_replenishQueueOnCore_ne st _ receiver hInv d h
    · rfl
  · rfl

/-- **The leg's state moves the replenish queue of the returned context's purge
core and no other** (`receiveReturnReplenishCores`). -/
theorem receiveLegState_replenishQueueOnCore_ne (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (d : Concurrency.CoreId)
    (h : d ∉ receiveReturnReplenishCores st receiver) :
    (receiveLegState st receiver).scheduler.replenishQueueOnCore d =
      st.scheduler.replenishQueueOnCore d :=
  receiveReturnSchedContext_replenishQueueOnCore_ne _ st receiver hInv d h

/-- A slot the receive's return finds a TCB in still holds a TCB. -/
theorem receiveReturnSchedContext_objects_eq_of_tcb (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) {oid : SeLe4n.ObjId} {y : TCB}
    (h : st.objects[oid]? = some (.tcb y)) :
    ∃ x, (receiveReturnSchedContext blocks st tid).objects[oid]? = some (.tcb x) :=
  let ⟨x, hx, _⟩ := receiveReturnSchedContext_tcb_fwd blocks st tid hInv oid y h
  ⟨x, hx⟩

/-- **The receive's return keeps every endpoint.** -/
theorem receiveReturnSchedContext_getEndpoint? (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (epId : SeLe4n.ObjId) :
    (receiveReturnSchedContext blocks st tid).getEndpoint? epId = st.getEndpoint? epId := by
  unfold SystemState.getEndpoint?
  rcases receiveReturnSchedContext_objects blocks st tid hInv epId with e | ⟨y, hy, e⟩ | ⟨sc, _, hs, e⟩
  · rw [e]
  · rw [e, hy]
  · rw [e, hs]

/-- **The compiled receive return.** -/
@[noinline] def receiveReturnSchedContextFast (blocks : Bool) (st : SystemState) (tCode : Nat) :
    SystemState :=
  if blocks then
    match st.getTcb? ⟨tCode⟩ with
    | some t =>
      if t.boundNotificationCode = 0 then st
      else maybeReturnSchedContextFast st (t.boundNotificationCode - 1) tCode
    | none => st
  else st

/-- **The compiled receive return is the receive return.** -/
theorem receiveReturnSchedContextFast_eq (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    receiveReturnSchedContextFast blocks st tid.val = receiveReturnSchedContext blocks st tid := by
  unfold receiveReturnSchedContextFast receiveReturnSchedContext
  split
  · show (match st.getTcb? tid with
      | some t => if t.boundNotificationCode = 0 then st
        else maybeReturnSchedContextFast st (t.boundNotificationCode - 1) tid.val
      | none => st) = _
    split
    · split
      · rfl
      · exact maybeReturnSchedContextFast_eq st ⟨_⟩ tid
    · rfl
  · rfl

end SeLe4n.Kernel
