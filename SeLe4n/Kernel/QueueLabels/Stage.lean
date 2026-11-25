-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.IpcPrimitives
import SeLe4n.Kernel.InformationFlow.Invariant.Composition
import SeLe4n.Kernel.IPC.CrossCore.NotificationBindDispatch

/-! # The waiters' stage: the unit a kernel entry chains

WS-SX SX11.2 (D38).  `endpointWaitersLabelsEqual` (every thread blocked
sending, calling or receiving on an endpoint has the endpoint's label) is
carried across a kernel entry the way the kernel records are (`RecordsStage`,
`KernelRecords/Frame.lean`): each step of the entry is a `QueueLabelsStage`, and
the stages compose.  Every writer of a thread's IPC state is one of three kinds:

* a **frame**: it keeps every thread's IPC state.  The records' frame
  (`RecordsFrame`) keeps every thread's record view, which holds its IPC state,
  so each of the records' frames is a waiters' frame with no new proof
  (`EndpointWaitersShrink.of_frame`);
* a **shrink**: it writes a state that waits on no endpoint (`.ready`, a reply
  block, a notification wait), or keeps one (`EndpointWaitersShrink`);
* a **creator**: it blocks one thread on one endpoint (`EndpointWaitersGrowAt`), and
  the entry that runs it discharges the new pair's labels from the gate it
  checks on that thread (`endpointFlowGate_implies_eq`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **An IPC state waiting on endpoint `e`**: blocked sending, calling or
receiving on it. -/
def ipcWaitsOnEndpoint (s : ThreadIpcState) (e : SeLe4n.ObjId) : Prop :=
  s = .blockedOnSend e ∨ s = .blockedOnCall e ∨ s = .blockedOnReceive e

@[simp] theorem ipcWaitsOnEndpoint_ready (e : SeLe4n.ObjId) : ¬ ipcWaitsOnEndpoint .ready e := by
  rintro (h | h | h) <;> cases h

@[simp] theorem ipcWaitsOnEndpoint_blockedOnReply (e o : SeLe4n.ObjId) (r : Option SeLe4n.ThreadId) :
    ¬ ipcWaitsOnEndpoint (.blockedOnReply o r) e := by
  rintro (h | h | h) <;> cases h

@[simp] theorem ipcWaitsOnEndpoint_blockedOnNotification (e n : SeLe4n.ObjId) :
    ¬ ipcWaitsOnEndpoint (.blockedOnNotification n) e := by
  rintro (h | h | h) <;> cases h

theorem ipcWaitsOnEndpoint_blockedOnSend {e e' : SeLe4n.ObjId}
    (h : ipcWaitsOnEndpoint (.blockedOnSend e) e') : e' = e := by
  rcases h with h | h | h <;> cases h; rfl

theorem ipcWaitsOnEndpoint_blockedOnCall {e e' : SeLe4n.ObjId}
    (h : ipcWaitsOnEndpoint (.blockedOnCall e) e') : e' = e := by
  rcases h with h | h | h <;> cases h; rfl

theorem ipcWaitsOnEndpoint_blockedOnReceive {e e' : SeLe4n.ObjId}
    (h : ipcWaitsOnEndpoint (.blockedOnReceive e) e') : e' = e := by
  rcases h with h | h | h <;> cases h; rfl

namespace endpointWaitersLabelsEqual

variable {ctx : LabelingContext} {st : SystemState}

/-- The pair read as one statement over every endpoint waiter. -/
theorem label (h : endpointWaitersLabelsEqual ctx st) {x : SeLe4n.ThreadId} {t : TCB}
    {e : SeLe4n.ObjId} (hL : lookupTcb st x = some t) (hW : ipcWaitsOnEndpoint t.ipcState e) :
    ctx.threadLabelOf x = ctx.endpointLabelOf e := by
  rcases hW with hW | hW | hW
  · exact h.1 x t e hL (.inl hW)
  · exact h.1 x t e hL (.inr hW)
  · exact h.2 x t e hL hW

theorem of_label
    (H : ∀ x t e, lookupTcb st x = some t → ipcWaitsOnEndpoint t.ipcState e →
      ctx.threadLabelOf x = ctx.endpointLabelOf e) :
    endpointWaitersLabelsEqual ctx st :=
  ⟨fun x t e hL hB => H x t e hL (hB.elim .inl (fun h => .inr (.inl h))),
   fun x t e hL hB => H x t e hL (.inr (.inr hB))⟩

end endpointWaitersLabelsEqual

/-- **A step that introduces no endpoint waiter**: every thread waiting on an
endpoint after it waited on the same endpoint before it. -/
def EndpointWaitersShrink (st st' : SystemState) : Prop :=
  ∀ (x : SeLe4n.ThreadId) (t' : TCB) (e : SeLe4n.ObjId), st'.getTcb? x = some t' →
    ipcWaitsOnEndpoint t'.ipcState e →
      ∃ t, st.getTcb? x = some t ∧ ipcWaitsOnEndpoint t.ipcState e

/-- **A step that blocks at most the thread `w` on the endpoint `e`**: every
other endpoint waiter after it waited on the same endpoint before it. -/
def EndpointWaitersGrowAt (w : SeLe4n.ThreadId) (e : SeLe4n.ObjId) (st st' : SystemState) : Prop :=
  ∀ (x : SeLe4n.ThreadId) (t' : TCB) (e' : SeLe4n.ObjId), st'.getTcb? x = some t' →
    ipcWaitsOnEndpoint t'.ipcState e' →
      (∃ t, st.getTcb? x = some t ∧ ipcWaitsOnEndpoint t.ipcState e') ∨ (x = w ∧ e' = e)

/-- **A step that carries the queue labels**: the endpoint waiters' labels and
the notifications' (`notificationLabelsAgree`).  The unit a kernel entry chains. -/
def QueueLabelsStage (ctx : LabelingContext) (st st' : SystemState) : Prop :=
  endpointWaitersLabelsEqual ctx st ∧ notificationLabelsAgree ctx st →
    endpointWaitersLabelsEqual ctx st' ∧ notificationLabelsAgree ctx st'

/-- A pre-state waiter read through `getTcb?` is one through `lookupTcb`, the
reserved identifiers aside. -/
theorem lookupTcb_of_getTcb?_of_lookupTcb {st st' : SystemState} {x : SeLe4n.ThreadId}
    {t t' : TCB} (hL : lookupTcb st' x = some t') (hG : st.getTcb? x = some t) :
    lookupTcb st x = some t :=
  lookupTcb_of_objects_of_not_reserved st x t ((SystemState.getTcb?_eq_some_iff _ _ _).mp hG)
    (lookupTcb_some_not_reserved st' x t' hL)

namespace EndpointWaitersShrink

theorem refl (st : SystemState) : EndpointWaitersShrink st st := fun _ t' _ h hW => ⟨t', h, hW⟩

theorem trans {a b c : SystemState} (h₁ : EndpointWaitersShrink a b) (h₂ : EndpointWaitersShrink b c) :
    EndpointWaitersShrink a c := fun x t'' e h hW => by
  obtain ⟨t', h', hW'⟩ := h₂ x t'' e h hW
  exact h₁ x t' e h' hW'

theorem of_eq {st st' : SystemState} (h : st' = st) : EndpointWaitersShrink st st' := by
  subst h; exact refl _

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    EndpointWaitersShrink st st' := fun x t' e hT hW =>
  ⟨t', by rw [SystemState.getTcb?_eq_some_iff] at hT ⊢; rwa [h] at hT, hW⟩

/-- **A records frame is a waiters' frame**: it keeps every thread's record
view, and the view holds the thread's IPC state. -/
theorem of_coreFrame {st st' : SystemState} (F : RecordsCoreFrame st st') :
    EndpointWaitersShrink st st' :=
  fun _ _ _ hT hW => by
    obtain ⟨t, hT0, hv⟩ := F.getTcb?_view hT
    exact ⟨t, hT0, (TcbRecordView.core_eq hv).2.1 ▸ hW⟩

theorem of_frame {st st' : SystemState} (F : RecordsFrame st st') : EndpointWaitersShrink st st' :=
  of_coreFrame F.core

/-- A shrink is a growth at any pair. -/
theorem growAt {st st' : SystemState} (h : EndpointWaitersShrink st st') (w : SeLe4n.ThreadId)
    (e : SeLe4n.ObjId) : EndpointWaitersGrowAt w e st st' := fun x t' e' hT hW => .inl (h x t' e' hT hW)

/-- **A shrink carries the waiters' labels.** -/
theorem waiters {ctx : LabelingContext} {st st' : SystemState} (h : EndpointWaitersShrink st st') :
    endpointWaitersLabelsEqual ctx st → endpointWaitersLabelsEqual ctx st' := fun hE => endpointWaitersLabelsEqual.of_label fun x t' e hL hW => by
  obtain ⟨t, hT, hW0⟩ := h x t' e (getTcb?_of_lookupTcb _ _ _ hL) hW
  exact hE.label (lookupTcb_of_getTcb?_of_lookupTcb hL hT) hW0

/-- A shrink onto a transition's state is a shrink onto the state it returns. -/
theorem of_fst_eq {α : Type} {st st' : SystemState} {p : SystemState × α} {r : α}
    (s : EndpointWaitersShrink st p.1) (h : p = (st', r)) : EndpointWaitersShrink st st' := by
  subst h; exact s

end EndpointWaitersShrink

namespace EndpointWaitersGrowAt

variable {w : SeLe4n.ThreadId} {e : SeLe4n.ObjId}

theorem trans_shrink {a b c : SystemState} (h₁ : EndpointWaitersGrowAt w e a b) (h₂ : EndpointWaitersShrink b c) :
    EndpointWaitersGrowAt w e a c := fun x t'' e' h hW => by
  obtain ⟨t', h', hW'⟩ := h₂ x t'' e' h hW
  exact h₁ x t' e' h' hW'

theorem shrink_trans {a b c : SystemState} (h₁ : EndpointWaitersShrink a b) (h₂ : EndpointWaitersGrowAt w e b c) :
    EndpointWaitersGrowAt w e a c := fun x t'' e' h hW => by
  rcases h₂ x t'' e' h hW with ⟨t', h', hW'⟩ | hN
  · exact .inl (h₁ x t' e' h' hW')
  · exact .inr hN

theorem trans {a b c : SystemState} (h₁ : EndpointWaitersGrowAt w e a b) (h₂ : EndpointWaitersGrowAt w e b c) :
    EndpointWaitersGrowAt w e a c := fun x t'' e' h hW => by
  rcases h₂ x t'' e' h hW with ⟨t', h', hW'⟩ | hN
  · exact h₁ x t' e' h' hW'
  · exact .inr hN

/-- **A growth at a pair of equal labels carries the waiters' labels**: the new
waiter's gate admitted it, so it has its endpoint's label. -/
theorem waiters {ctx : LabelingContext} {st st' : SystemState} (h : EndpointWaitersGrowAt w e st st')
    (hL : ctx.threadLabelOf w = ctx.endpointLabelOf e) :
    endpointWaitersLabelsEqual ctx st → endpointWaitersLabelsEqual ctx st' :=
  fun hE => endpointWaitersLabelsEqual.of_label fun x t' e' hLk hW => by
    rcases h x t' e' (getTcb?_of_lookupTcb _ _ _ hLk) hW with ⟨t, hT, hW0⟩ | ⟨rfl, rfl⟩
    · exact hE.label (lookupTcb_of_getTcb?_of_lookupTcb hLk hT) hW0
    · exact hL

theorem of_fst_eq {α : Type} {st st' : SystemState} {p : SystemState × α} {r : α}
    (s : EndpointWaitersGrowAt w e st p.1) (h : p = (st', r)) : EndpointWaitersGrowAt w e st st' := by
  subst h; exact s

end EndpointWaitersGrowAt

/-! ### Notification label coherence

`notificationEntryLabelsAgree` reads one object only, and of it only what
its record view holds (a thread's IPC state and its two queue links; a
notification's bound thread and its queue ends), so a records frame keeps it
(`NtfnLabelsKept.of_frame`).  The core frames that write those fields prove it
themselves; a wait or a bind adds one member, whose label its two-way gate
gives (`NtfnLabelsGrowAt`). -/

/-- What one object's coherence reads is its record view. -/
theorem notificationEntryLabelsAgree_of_view {ctx : LabelingContext} {oid : SeLe4n.ObjId}
    {a b : KernelObject} (h : recordViewOf (some a) = recordViewOf (some b)) :
    notificationEntryLabelsAgree ctx oid a = notificationEntryLabelsAgree ctx oid b := by
  cases a <;> cases b <;> simp only [recordViewOf, reduceCtorEq, Option.some.injEq,
    Sum.inl.injEq, Sum.inr.injEq] at h <;> try rfl
  · rename_i x y
    simp only [TCB.recordView, TcbRecordView.mk.injEq] at h
    obtain ⟨-, hI, -, -, hP, hN⟩ := h
    simp only [notificationEntryLabelsAgree, TCB.ntfnPrev, TCB.ntfnNext, hI, hP, hN]
  · rename_i x y
    simp only [Notification.recordView, Prod.mk.injEq] at h
    obtain ⟨hB, hH, hT⟩ := h
    simp only [notificationEntryLabelsAgree, Notification.boundTCB, Notification.waitHead,
      Notification.waitTail, hB, hH, hT]

/-- An object with no record view carries no coherence obligation. -/
theorem notificationEntryLabelsAgree_of_view_none {ctx : LabelingContext} {oid : SeLe4n.ObjId}
    {a : KernelObject} (h : recordViewOf (some a) = none) :
    notificationEntryLabelsAgree ctx oid a := by
  cases a <;> simp_all [recordViewOf, notificationEntryLabelsAgree]

/-- **A step that keeps notification label coherence**, under every labelling. -/
def NtfnLabelsKept (st st' : SystemState) : Prop :=
  ∀ ctx : LabelingContext, notificationLabelsAgree ctx st → notificationLabelsAgree ctx st'

/-- **A step that adds at most the thread `w` to the notification `n`**: it
keeps coherence under every labelling whose gate admits `w` at `n`. -/
def NtfnLabelsGrowAt (w : SeLe4n.ThreadId) (n : SeLe4n.ObjId) (st st' : SystemState) : Prop :=
  ∀ ctx : LabelingContext, notificationFlowGate ctx n w = true →
    notificationLabelsAgree ctx st → notificationLabelsAgree ctx st'

namespace NtfnLabelsKept

theorem refl (st : SystemState) : NtfnLabelsKept st st := fun _ h => h

theorem trans {a b c : SystemState} (h₁ : NtfnLabelsKept a b) (h₂ : NtfnLabelsKept b c) :
    NtfnLabelsKept a c := fun ctx h => h₂ ctx (h₁ ctx h)

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    NtfnLabelsKept st st' := fun _ H oid obj hO => H oid obj (h ▸ hO)

theorem of_eq {st st' : SystemState} (h : st' = st) : NtfnLabelsKept st st' := by
  subst h; exact refl _

/-- **Every slot's record view kept keeps coherence.** -/
theorem of_views {st st' : SystemState}
    (hV : ∀ k : SeLe4n.ObjId, recordViewOf st'.objects[k]? = recordViewOf st.objects[k]?) :
    NtfnLabelsKept st st' := fun _ H oid obj' hO => by
  have hv := hV oid
  rw [hO] at hv
  cases hS : st.objects[oid]? with
  | none => rw [hS] at hv; exact notificationEntryLabelsAgree_of_view_none hv
  | some obj =>
    rw [hS] at hv
    rw [notificationEntryLabelsAgree_of_view hv]
    exact H oid obj hS

/-- **A records frame keeps coherence**, with no new proof. -/
theorem of_frame {st st' : SystemState} (F : RecordsFrame st st') : NtfnLabelsKept st st' :=
  of_views F.views

/-- What one object's coherence reads is its core view and its notification-queue
reads. -/
theorem _root_.SeLe4n.Kernel.notificationEntryLabelsAgree_of_coreView
    {ctx : LabelingContext} {oid : SeLe4n.ObjId} {a b : KernelObject}
    (hC : recordCoreViewOf (some a) = recordCoreViewOf (some b))
    (hN : recordNtfnViewOf (some a) = recordNtfnViewOf (some b)) :
    notificationEntryLabelsAgree ctx oid a = notificationEntryLabelsAgree ctx oid b := by
  cases a <;> cases b <;> simp only [recordCoreViewOf, recordViewOf, recordCoreView,
    recordNtfnViewOf, Option.map_some, Option.map_none, reduceCtorEq, Option.some.injEq,
    Sum.inl.injEq, Sum.inr.injEq] at hC hN <;> try rfl
  · rename_i x y
    simp only [TCB.recordView, TcbRecordView.core, TcbRecordView.mk.injEq] at hC
    simp only [Prod.mk.injEq] at hN
    simp only [notificationEntryLabelsAgree, TCB.ntfnPrev, TCB.ntfnNext, hC.2.1, hN.1, hN.2]
  · rename_i x y
    simp only [Notification.recordView, Prod.mk.injEq] at hN
    obtain ⟨hB, hH, hT⟩ := hN
    simp only [notificationEntryLabelsAgree, Notification.boundTCB, Notification.waitHead,
      Notification.waitTail, hB, hH, hT]

/-- **An endpoint-queue write keeps coherence**, with no new proof. -/
theorem of_endpointFrame {st st' : SystemState} (F : RecordsEndpointFrame st st') :
    NtfnLabelsKept st st' := fun _ H oid obj' hO => by
  have hc := F.core.views oid
  have hn := F.ntfnViews oid
  rw [hO] at hc hn
  cases hS : st.objects[oid]? with
  | none => rw [hS] at hc; cases obj' <;> simp [recordCoreViewOf, recordViewOf] at hc <;>
      simp [notificationEntryLabelsAgree]
  | some obj =>
    rw [hS] at hc hn
    rw [notificationEntryLabelsAgree_of_coreView hc hn]
    exact H oid obj hS

/-- A kept step is a growth at any member. -/
theorem growAt {st st' : SystemState} (h : NtfnLabelsKept st st') (w : SeLe4n.ThreadId)
    (n : SeLe4n.ObjId) : NtfnLabelsGrowAt w n st st' := fun ctx _ H => h ctx H

theorem of_fst_eq {α : Type} {st st' : SystemState} {p : SystemState × α} {r : α}
    (s : NtfnLabelsKept st p.1) (h : p = (st', r)) : NtfnLabelsKept st st' := by
  subst h; exact s

/-- **One slot rewritten**: the other slots kept, and the rewritten object's
coherence read off the pre-state's. -/
theorem of_slot {st st' : SystemState} {k : SeLe4n.ObjId}
    (hNe : ∀ j, j ≠ k → st'.objects[j]? = st.objects[j]?)
    (hSelf : ∀ ctx, notificationLabelsAgree ctx st → ∀ o', st'.objects[k]? = some o' →
      notificationEntryLabelsAgree ctx k o') : NtfnLabelsKept st st' :=
  fun ctx H oid obj' hO => by
    by_cases hk : oid = k
    · subst hk; exact hSelf ctx H obj' hO
    · rw [hNe _ hk] at hO; exact H oid obj' hO

end NtfnLabelsKept

namespace NtfnLabelsGrowAt

variable {w : SeLe4n.ThreadId} {n : SeLe4n.ObjId}

theorem trans_kept {a b c : SystemState} (h₁ : NtfnLabelsGrowAt w n a b) (h₂ : NtfnLabelsKept b c) :
    NtfnLabelsGrowAt w n a c := fun ctx hG H => h₂ ctx (h₁ ctx hG H)

theorem kept_trans {a b c : SystemState} (h₁ : NtfnLabelsKept a b) (h₂ : NtfnLabelsGrowAt w n b c) :
    NtfnLabelsGrowAt w n a c := fun ctx hG H => h₂ ctx hG (h₁ ctx H)

theorem trans {a b c : SystemState} (h₁ : NtfnLabelsGrowAt w n a b) (h₂ : NtfnLabelsGrowAt w n b c) :
    NtfnLabelsGrowAt w n a c := fun ctx hG H => h₂ ctx hG (h₁ ctx hG H)

end NtfnLabelsGrowAt

namespace QueueLabelsStage

variable {ctx : LabelingContext}

theorem refl (st : SystemState) : QueueLabelsStage ctx st st := id

theorem trans {a b c : SystemState} (h₁ : QueueLabelsStage ctx a b) (h₂ : QueueLabelsStage ctx b c) :
    QueueLabelsStage ctx a c := h₂ ∘ h₁

theorem of_eq {st st' : SystemState} (h : st' = st) : QueueLabelsStage ctx st st' := by
  subst h; exact refl _

/-- The two halves, each carried. -/
theorem of_parts {st st' : SystemState}
    (hE : endpointWaitersLabelsEqual ctx st → endpointWaitersLabelsEqual ctx st')
    (hN : notificationLabelsAgree ctx st → notificationLabelsAgree ctx st') : QueueLabelsStage ctx st st' :=
  fun h => ⟨hE h.1, hN h.2⟩

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    QueueLabelsStage ctx st st' :=
  of_parts (EndpointWaitersShrink.of_objects_eq h).waiters (NtfnLabelsKept.of_objects_eq h ctx)

theorem of_frame {st st' : SystemState} (F : RecordsFrame st st') : QueueLabelsStage ctx st st' :=
  of_parts (EndpointWaitersShrink.of_frame F).waiters (NtfnLabelsKept.of_frame F ctx)

theorem of_fst_eq {α : Type} {st st' : SystemState} {p : SystemState × α} {r : α}
    (s : QueueLabelsStage ctx st p.1) (h : p = (st', r)) : QueueLabelsStage ctx st st' := by
  subst h; exact s

end QueueLabelsStage

/-! ### The frames: the relations with the store's invariant

A step's relations and the store's invariant at the state it reaches, which the
next step's frames read (`LendersFrame`'s shape). -/

/-- **A step that introduces no endpoint waiter and keeps notification label
coherence**, with the store's invariant. -/
structure QueueLabelsFrame (st st' : SystemState) : Prop where
  shrink : EndpointWaitersShrink st st'
  ntfn : NtfnLabelsKept st st'
  invExt : st'.objects.invExt

/-- **A step that blocks at most `w` on the endpoint `e`**, keeping coherence,
with the store's invariant. -/
structure QueueLabelsGrowFrame (w : SeLe4n.ThreadId) (e : SeLe4n.ObjId) (st st' : SystemState) : Prop where
  grow : EndpointWaitersGrowAt w e st st'
  ntfn : NtfnLabelsKept st st'
  invExt : st'.objects.invExt

/-- **A step that adds at most `w` to the notification `n`** (a wait, a bind)
and introduces no endpoint waiter, with the store's invariant. -/
structure QueueLabelsNtfnGrowFrame (w : SeLe4n.ThreadId) (n : SeLe4n.ObjId) (st st' : SystemState) :
    Prop where
  shrink : EndpointWaitersShrink st st'
  ntfn : NtfnLabelsGrowAt w n st st'
  invExt : st'.objects.invExt

namespace QueueLabelsFrame

theorem refl {st : SystemState} (h : st.objects.invExt) : QueueLabelsFrame st st :=
  ⟨.refl _, .refl _, h⟩

theorem trans {a b c : SystemState} (F : QueueLabelsFrame a b) (G : QueueLabelsFrame b c) :
    QueueLabelsFrame a c := ⟨F.shrink.trans G.shrink, NtfnLabelsKept.trans F.ntfn G.ntfn, G.invExt⟩

theorem andThen {a b c : SystemState} (F : QueueLabelsFrame a b)
    (G : b.objects.invExt → QueueLabelsFrame b c) : QueueLabelsFrame a c := F.trans (G F.invExt)

theorem of_frame {st st' : SystemState} (F : RecordsFrame st st') : QueueLabelsFrame st st' :=
  ⟨.of_frame F, .of_frame F, F.invExt⟩

/-- A core frame, with its coherence proved. -/
theorem of_coreFrame {st st' : SystemState} (F : RecordsCoreFrame st st')
    (hN : NtfnLabelsKept st st') : QueueLabelsFrame st st' :=
  ⟨.of_coreFrame F, hN, F.invExt⟩

/-- An endpoint-queue write. -/
theorem of_endpointFrame {st st' : SystemState} (F : RecordsEndpointFrame st st') :
    QueueLabelsFrame st st' :=
  of_coreFrame F.core (.of_endpointFrame F)

theorem of_eq {st st' : SystemState} (hInv : st.objects.invExt) (h : st' = st) :
    QueueLabelsFrame st st' := by subst h; exact refl hInv

theorem growAt {st st' : SystemState} (F : QueueLabelsFrame st st') (w : SeLe4n.ThreadId)
    (e : SeLe4n.ObjId) : QueueLabelsGrowFrame w e st st' := ⟨F.shrink.growAt w e, F.ntfn, F.invExt⟩

theorem ntfnGrowAt {st st' : SystemState} (F : QueueLabelsFrame st st') (w : SeLe4n.ThreadId)
    (n : SeLe4n.ObjId) : QueueLabelsNtfnGrowFrame w n st st' := ⟨F.shrink, NtfnLabelsKept.growAt F.ntfn w n, F.invExt⟩

/-- A frame followed by a growth is a growth. -/
theorem thenGrow {a b c : SystemState} {w : SeLe4n.ThreadId} {e : SeLe4n.ObjId}
    (F : QueueLabelsFrame a b) (G : QueueLabelsGrowFrame w e b c) : QueueLabelsGrowFrame w e a c :=
  ⟨EndpointWaitersGrowAt.shrink_trans F.shrink G.grow, NtfnLabelsKept.trans F.ntfn G.ntfn, G.invExt⟩

theorem thenNtfnGrow {a b c : SystemState} {w : SeLe4n.ThreadId} {n : SeLe4n.ObjId}
    (F : QueueLabelsFrame a b) (G : QueueLabelsNtfnGrowFrame w n b c) :
    QueueLabelsNtfnGrowFrame w n a c :=
  ⟨F.shrink.trans G.shrink, NtfnLabelsGrowAt.kept_trans F.ntfn G.ntfn, G.invExt⟩

theorem stage {ctx : LabelingContext} {st st' : SystemState} (F : QueueLabelsFrame st st') :
    QueueLabelsStage ctx st st' := .of_parts F.shrink.waiters (F.ntfn ctx)

/-- The endpoint waiters' half alone, for a consumer that reads no notification. -/
theorem waiters {ctx : LabelingContext} {st st' : SystemState} (F : QueueLabelsFrame st st') :
    endpointWaitersLabelsEqual ctx st → endpointWaitersLabelsEqual ctx st' := F.shrink.waiters

theorem of_fst_eq {α : Type} {st st' : SystemState} {p : SystemState × α} {r : α}
    (s : QueueLabelsFrame st p.1) (h : p = (st', r)) : QueueLabelsFrame st st' := by subst h; exact s

end QueueLabelsFrame

namespace QueueLabelsGrowFrame

variable {w : SeLe4n.ThreadId} {e : SeLe4n.ObjId}

theorem thenFrame {a b c : SystemState} (G : QueueLabelsGrowFrame w e a b) (F : QueueLabelsFrame b c) :
    QueueLabelsGrowFrame w e a c := ⟨G.grow.trans_shrink F.shrink, NtfnLabelsKept.trans G.ntfn F.ntfn, F.invExt⟩

theorem andThen {a b c : SystemState} (G : QueueLabelsGrowFrame w e a b)
    (F : b.objects.invExt → QueueLabelsFrame b c) : QueueLabelsGrowFrame w e a c := G.thenFrame (F G.invExt)

theorem refl {st : SystemState} (h : st.objects.invExt) : QueueLabelsGrowFrame w e st st :=
  (QueueLabelsFrame.refl h).growAt w e

theorem stage {ctx : LabelingContext} {st st' : SystemState} (G : QueueLabelsGrowFrame w e st st')
    (hL : ctx.threadLabelOf w = ctx.endpointLabelOf e) : QueueLabelsStage ctx st st' :=
  .of_parts (G.grow.waiters hL) (G.ntfn ctx)

/-- The endpoint waiters' half alone. -/
theorem waiters {ctx : LabelingContext} {st st' : SystemState} (G : QueueLabelsGrowFrame w e st st')
    (hL : ctx.threadLabelOf w = ctx.endpointLabelOf e) :
    endpointWaitersLabelsEqual ctx st → endpointWaitersLabelsEqual ctx st' := G.grow.waiters hL

theorem of_fst_eq {α : Type} {st st' : SystemState} {p : SystemState × α} {r : α}
    (s : QueueLabelsGrowFrame w e st p.1) (h : p = (st', r)) : QueueLabelsGrowFrame w e st st' := by
  subst h; exact s

end QueueLabelsGrowFrame

namespace QueueLabelsNtfnGrowFrame

variable {w : SeLe4n.ThreadId} {n : SeLe4n.ObjId}

theorem thenFrame {a b c : SystemState} (G : QueueLabelsNtfnGrowFrame w n a b) (F : QueueLabelsFrame b c) :
    QueueLabelsNtfnGrowFrame w n a c := ⟨G.shrink.trans F.shrink, NtfnLabelsGrowAt.trans_kept G.ntfn F.ntfn, F.invExt⟩

theorem andThen {a b c : SystemState} (G : QueueLabelsNtfnGrowFrame w n a b)
    (F : b.objects.invExt → QueueLabelsFrame b c) : QueueLabelsNtfnGrowFrame w n a c :=
  G.thenFrame (F G.invExt)

theorem refl {st : SystemState} (h : st.objects.invExt) : QueueLabelsNtfnGrowFrame w n st st :=
  (QueueLabelsFrame.refl h).ntfnGrowAt w n

/-- **A growth whose member the gate admitted carries the queue labels.** -/
theorem stage {ctx : LabelingContext} {st st' : SystemState} (G : QueueLabelsNtfnGrowFrame w n st st')
    (hG : notificationFlowGate ctx n w = true) : QueueLabelsStage ctx st st' :=
  .of_parts G.shrink.waiters (G.ntfn ctx hG)

theorem of_fst_eq {α : Type} {st st' : SystemState} {p : SystemState × α} {r : α}
    (s : QueueLabelsNtfnGrowFrame w n st p.1) (h : p = (st', r)) : QueueLabelsNtfnGrowFrame w n st st' := by
  subst h; exact s

end QueueLabelsNtfnGrowFrame

/-- **A step that keeps the queue labels under the labelling `ctx`**: no new
endpoint waiter, agreement under `ctx` kept, with the store's invariant.  What a
checked wait or bind is: its gate admits its new member under the labelling it
checks, and only that one. -/
structure QueueLabelsGatedFrame (ctx : LabelingContext) (st st' : SystemState) : Prop where
  shrink : EndpointWaitersShrink st st'
  ntfn : notificationLabelsAgree ctx st → notificationLabelsAgree ctx st'
  invExt : st'.objects.invExt

namespace QueueLabelsGatedFrame

variable {ctx : LabelingContext}

theorem of_frame {st st' : SystemState} (F : QueueLabelsFrame st st') : QueueLabelsGatedFrame ctx st st' :=
  ⟨F.shrink, F.ntfn ctx, F.invExt⟩

theorem refl {st : SystemState} (h : st.objects.invExt) : QueueLabelsGatedFrame ctx st st :=
  of_frame (.refl h)

theorem trans {a b c : SystemState} (F : QueueLabelsGatedFrame ctx a b) (G : QueueLabelsGatedFrame ctx b c) :
    QueueLabelsGatedFrame ctx a c := ⟨F.shrink.trans G.shrink, G.ntfn ∘ F.ntfn, G.invExt⟩

theorem andThen {a b c : SystemState} (F : QueueLabelsGatedFrame ctx a b)
    (G : b.objects.invExt → QueueLabelsFrame b c) : QueueLabelsGatedFrame ctx a c :=
  F.trans (of_frame (G F.invExt))

theorem stage {st st' : SystemState} (F : QueueLabelsGatedFrame ctx st st') : QueueLabelsStage ctx st st' :=
  .of_parts F.shrink.waiters F.ntfn

theorem of_fst_eq {α : Type} {st st' : SystemState} {p : SystemState × α} {r : α}
    (s : QueueLabelsGatedFrame ctx st p.1) (h : p = (st', r)) : QueueLabelsGatedFrame ctx st st' := by
  subst h; exact s

end QueueLabelsGatedFrame

/-- A growth whose member the gate admits under `ctx` keeps the labels under `ctx`. -/
theorem QueueLabelsNtfnGrowFrame.gated {ctx : LabelingContext} {w : SeLe4n.ThreadId} {n : SeLe4n.ObjId}
    {st st' : SystemState} (G : QueueLabelsNtfnGrowFrame w n st st')
    (hG : notificationFlowGate ctx n w = true) : QueueLabelsGatedFrame ctx st st' :=
  ⟨G.shrink, G.ntfn ctx hG, G.invExt⟩

/-! ### One thread's write -/

/-- **A thread write that blocks it on no new endpoint**: the thread after the
write waits on an endpoint only where it waited before. -/
def TcbWaitsKept (x y : TCB) : Prop :=
  ∀ e, ipcWaitsOnEndpoint y.ipcState e → ipcWaitsOnEndpoint x.ipcState e

theorem TcbWaitsKept.of_ipc {x y : TCB} (h : y.ipcState = x.ipcState) : TcbWaitsKept x y :=
  fun _ hW => h ▸ hW

theorem TcbWaitsKept.of_noWait {x y : TCB} (h : ∀ e, ¬ ipcWaitsOnEndpoint y.ipcState e) :
    TcbWaitsKept x y := fun e hW => absurd hW (h e)

/-- The per-slot shape of a one-thread write, as a growth at that thread. -/
theorem EndpointWaitersGrowAt.of_slot {st st' : SystemState} {t : SeLe4n.ThreadId} {e0 : SeLe4n.ObjId}
    (hNe : ∀ k, k ≠ t.toObjId → st'.objects[k]? = st.objects[k]?)
    (hSelf : ∀ y, st'.objects[t.toObjId]? = some (.tcb y) → ∀ e, ipcWaitsOnEndpoint y.ipcState e →
      (∃ x, st.objects[t.toObjId]? = some (.tcb x) ∧ ipcWaitsOnEndpoint x.ipcState e) ∨ e = e0) :
    EndpointWaitersGrowAt t e0 st st' := fun u t' e hT hW => by
  have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
  by_cases hk : u.toObjId = t.toObjId
  · rw [hk] at hO
    rcases hSelf t' hO e hW with ⟨x, hx, hWx⟩ | rfl
    · exact .inl ⟨x, (SystemState.getTcb?_eq_some_iff _ _ _).mpr (hk ▸ hx), hWx⟩
    · exact .inr ⟨SeLe4n.ThreadId.toObjId_injective _ _ hk, rfl⟩
  · rw [hNe _ hk] at hO
    exact .inl ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO, hW⟩

theorem EndpointWaitersShrink.of_slot {st st' : SystemState} {t : SeLe4n.ThreadId}
    (hNe : ∀ k, k ≠ t.toObjId → st'.objects[k]? = st.objects[k]?)
    (hSelf : ∀ y, st'.objects[t.toObjId]? = some (.tcb y) → ∀ e, ipcWaitsOnEndpoint y.ipcState e →
      ∃ x, st.objects[t.toObjId]? = some (.tcb x) ∧ ipcWaitsOnEndpoint x.ipcState e) :
    EndpointWaitersShrink st st' := fun u t' e hT hW => by
  have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
  by_cases hk : u.toObjId = t.toObjId
  · rw [hk] at hO
    obtain ⟨x, hx, hWx⟩ := hSelf t' hO e hW
    exact ⟨x, (SystemState.getTcb?_eq_some_iff _ _ _).mpr (hk ▸ hx), hWx⟩
  · rw [hNe _ hk] at hO
    exact ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO, hW⟩

/-- **A thread write that keeps its share of notification label coherence**,
under every labelling. -/
def TcbNtfnKept (x y : TCB) : Prop :=
  ∀ (ctx : LabelingContext) (oid : SeLe4n.ObjId),
    notificationEntryLabelsAgree ctx oid (.tcb x) →
      notificationEntryLabelsAgree ctx oid (.tcb y)

namespace TcbNtfnKept

theorem refl (x : TCB) : TcbNtfnKept x x := fun _ _ h => h

/-- A write of neither the IPC state nor the queue links. -/
theorem of_fields {x y : TCB} (hI : y.ipcState = x.ipcState)
    (hP : y.ntfnPrevCode = x.ntfnPrevCode) (hN : y.ntfnNextCode = x.ntfnNextCode) :
    TcbNtfnKept x y := fun _ _ h => by
  simp only [notificationEntryLabelsAgree] at h ⊢
  refine ⟨fun n hn => h.1 n (hI ▸ hn), fun u hu => h.2.1 u ?_, fun u hu => h.2.2 u ?_⟩
  · unfold TCB.ntfnPrev at hu ⊢; rw [← hP]; exact hu
  · unfold TCB.ntfnNext at hu ⊢; rw [← hN]; exact hu

/-- **A write that leaves the thread blocked on no notification**, its links
kept: what the thread's share then asks of it is its links' labels, which the
write keeps. -/
theorem of_notBlocked {x y : TCB} (hy : ∀ n, y.ipcState ≠ .blockedOnNotification n)
    (hP : y.ntfnPrevCode = x.ntfnPrevCode := by rfl) (hN : y.ntfnNextCode = x.ntfnNextCode := by rfl) :
    TcbNtfnKept x y := fun _ _ h =>
  ⟨fun n hn => absurd hn (hy n), fun u hu => h.2.1 u (by unfold TCB.ntfnPrev at hu ⊢; rw [← hP]; exact hu),
   fun u hu => h.2.2 u (by unfold TCB.ntfnNext at hu ⊢; rw [← hN]; exact hu)⟩

/-- **An IPC-state write** of a state blocked on no notification, the links
kept. -/
theorem setIpcState {x y : TCB} {s : ThreadIpcState}
    (hs : ∀ n, s ≠ .blockedOnNotification n := by intro n h; cases h)
    (hP : y.ntfnPrevCode = x.ntfnPrevCode := by rfl) (hN : y.ntfnNextCode = x.ntfnNextCode := by rfl) :
    TcbNtfnKept x (y.setIpcState s) :=
  of_notBlocked (fun n => by rw [TCB.ipcState_setIpcState]; exact hs n) hP hN

end TcbNtfnKept

/-- Closes a thread write's agreement obligation where the write keeps both
queue links and keeps the IPC state or writes one blocked on no notification. -/
macro "tcb_ntfn_kept" : tactic =>
  `(tactic| (intros; first
    | exact TcbNtfnKept.of_fields rfl rfl rfl
    | exact TcbNtfnKept.setIpcState
    | exact TcbNtfnKept.of_notBlocked (fun _ h => by simp at h)))

namespace NtfnLabelsKept

/-- **A raw insert over a slot**, its object's share read off the slot's. -/
theorem insert {st : SystemState} {k : SeLe4n.ObjId} {o : KernelObject} (hInv : st.objects.invExt)
    (hSelf : ∀ ctx, notificationLabelsAgree ctx st → notificationEntryLabelsAgree ctx k o) :
    NtfnLabelsKept st { st with objects := st.objects.insert k o } :=
  of_slot (fun j hj => by
      show (st.objects.insert k o)[j]? = _
      simp only [RHTable_getElem?_eq_get?]
      exact RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hj (eq_of_beq hb).symm) hInv)
    fun ctx H o' hO => by
      have : (st.objects.insert k o)[k]? = some o := by
        simp only [RHTable_getElem?_eq_get?]; exact RobinHood.RHTable.getElem?_insert_self _ _ _ hInv
      rw [show ({ st with objects := st.objects.insert k o } : SystemState).objects[k]? = _ from this] at hO
      cases hO; exact hSelf ctx H

/-- **A TCB stored over a TCB.** -/
theorem storeObject_tcb {st st' : SystemState} {t : SeLe4n.ThreadId} {x y : TCB}
    (hInv : st.objects.invExt) (hOld : st.objects[t.toObjId]? = some (.tcb x))
    (h : storeObject t.toObjId (.tcb y) st = .ok ((), st')) (hN : TcbNtfnKept x y) :
    NtfnLabelsKept st st' :=
  of_slot (fun k hk => storeObject_objects_ne st st' _ k _ hk hInv h) fun ctx H o' hO => by
    rw [storeObject_objects_eq st st' _ _ hInv h] at hO
    cases hO; exact hN ctx _ (H _ _ hOld)

/-- **The unchecked TCB write.** -/
theorem updateTcb (st : SystemState) (t : SeLe4n.ThreadId) {f : TCB → TCB}
    (hInv : st.objects.invExt)
    (hN : ∀ x, st.objects[t.toObjId]? = some (.tcb x) → TcbNtfnKept x (f x)) :
    NtfnLabelsKept st (st.updateTcb t f) := by
  cases hT : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact refl _
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hT]
    have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
    exact insert hInv fun ctx H => hN x hO ctx _ (H _ _ hO)

/-- **A thread rewritten in its slot.** -/
theorem mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId) {g : TCB → TCB}
    (hN : ∀ x, st.objects[t.toObjId]? = some (.tcb x) → TcbNtfnKept x (g x)) :
    NtfnLabelsKept st (st.mapTcbInPlace t g) :=
  of_slot (k := t.toObjId) (fun j hj => by
      rw [SystemState.objects_mapTcbInPlace]
      simp only [beq_iff_eq, show ¬ t.toObjId = j from fun e => hj e.symm, if_false])
    fun ctx H o' hO => by
      rw [SystemState.objects_mapTcbInPlace] at hO
      simp only [beq_self_eq_true, if_true] at hO
      cases hS : st.objects[t.toObjId]? with
      | none => rw [hS] at hO; cases hO
      | some o =>
        rw [hS] at hO
        cases o <;> simp only [Option.map_some, KernelObject.mapTcb, Option.some.injEq] at hO <;>
          subst hO <;> first | exact hN _ hS ctx _ (H _ _ hS) | exact H _ _ hS

end NtfnLabelsKept

namespace QueueLabelsFrame

/-- **A TCB stored over a TCB**, keeping its waits: the endpoint half. -/
theorem _root_.SeLe4n.Kernel.EndpointWaitersShrink.storeObject_tcb {st st' : SystemState}
    {t : SeLe4n.ThreadId} {x y : TCB}
    (hInv : st.objects.invExt) (hOld : st.objects[t.toObjId]? = some (.tcb x))
    (h : storeObject t.toObjId (.tcb y) st = .ok ((), st')) (hS : TcbWaitsKept x y) :
    EndpointWaitersShrink st st' :=
  EndpointWaitersShrink.of_slot (fun k hk => storeObject_objects_ne st st' _ k _ hk hInv h)
    fun y' hy e hW => by
      rw [storeObject_objects_eq st st' _ _ hInv h] at hy
      cases hy
      exact ⟨x, hOld, hS e hW⟩

/-- **A TCB stored over a TCB**, keeping its waits. -/
theorem storeObject_tcb {st st' : SystemState} {t : SeLe4n.ThreadId} {x y : TCB}
    (hInv : st.objects.invExt) (hOld : st.objects[t.toObjId]? = some (.tcb x))
    (h : storeObject t.toObjId (.tcb y) st = .ok ((), st')) (hS : TcbWaitsKept x y)
    (hN : TcbNtfnKept x y := by tcb_ntfn_kept) :
    QueueLabelsFrame st st' :=
  ⟨.storeObject_tcb hInv hOld h hS, NtfnLabelsKept.storeObject_tcb hInv hOld h hN,
    storeObject_preserves_objects_invExt st st' _ _ hInv h⟩

/-- **The checked TCB write**, keeping the thread's waits. -/
theorem modifyTcb {st st' : SystemState} {t : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.modifyTcb st t f = .ok st')
    (hS : ∀ x, TcbWaitsKept x (f x))
    (hN : ∀ x, st.objects[t.toObjId]? = some (.tcb x) → TcbNtfnKept x (f x) := by tcb_ntfn_kept) :
    QueueLabelsFrame st st' := by
  obtain ⟨tcb, hL, hSt⟩ := modifyTcb_ok_decompose h
  have hO := lookupTcb_some_objects st t tcb hL
  exact storeObject_tcb hInv hO hSt (hS tcb) (hN tcb hO)

theorem updateTcb_shrink (st : SystemState) (t : SeLe4n.ThreadId) {f : TCB → TCB}
    (hInv : st.objects.invExt) (hS : ∀ x, TcbWaitsKept x (f x)) :
    EndpointWaitersShrink st (st.updateTcb t f) := fun u t' e hT hW => by
  by_cases hk : t.toObjId = u.toObjId
  · have hu : u = t := (SeLe4n.ThreadId.toObjId_injective _ _ hk).symm
    subst hu
    rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv] at hT
    cases hX : st.getTcb? u with
    | none => rw [hX] at hT; cases hT
    | some x => rw [hX] at hT; cases hT; exact ⟨x, rfl, hS x e hW⟩
  · rw [SystemState.updateTcb_getTcb?_ne _ _ _ hInv _ hk] at hT
    exact ⟨t', hT, hW⟩

/-- **The unchecked TCB write**, likewise. -/
theorem updateTcb (st : SystemState) (t : SeLe4n.ThreadId) {f : TCB → TCB}
    (hInv : st.objects.invExt) (hS : ∀ x, TcbWaitsKept x (f x))
    (hN : ∀ x, st.objects[t.toObjId]? = some (.tcb x) → TcbNtfnKept x (f x) := by tcb_ntfn_kept) :
    QueueLabelsFrame st (st.updateTcb t f) :=
  ⟨updateTcb_shrink st t hInv hS, NtfnLabelsKept.updateTcb st t hInv hN,
    SystemState.updateTcb_preserves_objects_invExt st t f hInv⟩

/-- An IPC-state and message store of a state waiting on no endpoint. -/
theorem storeTcbIpcStateAndMessage {st st' : SystemState} {t : SeLe4n.ThreadId}
    {s : ThreadIpcState} {m : Option IpcMessage} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.storeTcbIpcStateAndMessage st t s m = .ok st')
    (hs : ∀ e, ¬ ipcWaitsOnEndpoint s e := by intro e; simp)
    (hN : ∀ x, st.objects[t.toObjId]? = some (.tcb x) →
      TcbNtfnKept x (TCB.setIpcState { x with pendingMessage := m } s) := by tcb_ntfn_kept) :
    QueueLabelsFrame st st' :=
  modifyTcb hInv h (fun _ => TcbWaitsKept.of_noWait (by simpa using hs)) hN

theorem storeTcbIpcState {st st' : SystemState} {t : SeLe4n.ThreadId} {s : ThreadIpcState}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.storeTcbIpcState st t s = .ok st')
    (hs : ∀ e, ¬ ipcWaitsOnEndpoint s e := by intro e; simp)
    (hN : ∀ x, st.objects[t.toObjId]? = some (.tcb x) → TcbNtfnKept x (x.setIpcState s) := by
      tcb_ntfn_kept) :
    QueueLabelsFrame st st' :=
  modifyTcb hInv h (fun _ => TcbWaitsKept.of_noWait (by simpa using hs)) hN

theorem storeTcbReceiveComplete {st st' : SystemState} {t : SeLe4n.ThreadId}
    {m : Option IpcMessage} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.storeTcbReceiveComplete st t m = .ok st')
    (hN : ∀ x, st.objects[t.toObjId]? = some (.tcb x) →
      TcbNtfnKept x (TCB.setIpcState { x with pendingMessage := m, pendingReceiveReplyCode := 0 } .ready) := by
      tcb_ntfn_kept) :
    QueueLabelsFrame st st' :=
  modifyTcb hInv h (fun _ => TcbWaitsKept.of_noWait (by simp)) hN

/-- **A thread rewritten in its slot**, keeping its waits. -/
theorem mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId) {g : TCB → TCB}
    (hInv : st.objects.invExt) (hS : ∀ x, TcbWaitsKept x (g x))
    (hN : ∀ x, st.objects[t.toObjId]? = some (.tcb x) → TcbNtfnKept x (g x) := by tcb_ntfn_kept) :
    QueueLabelsFrame st (st.mapTcbInPlace t g) := by
  refine ⟨fun u tcb' e hU hW => ?_, NtfnLabelsKept.mapTcbInPlace st t hN,
    SystemState.mapTcbInPlace_objects_invExt _ _ _ hInv⟩
  by_cases hk : t.toObjId = u.toObjId
  · have hu : u = t := (SeLe4n.ThreadId.toObjId_injective _ _ hk).symm
    subst hu
    rw [SystemState.mapTcbInPlace_getTcb?_self] at hU
    cases hT : st.getTcb? u with
    | none => rw [hT] at hU; cases hU
    | some x => rw [hT] at hU; cases hU; exact ⟨x, rfl, hS x e hW⟩
  · rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hk] at hU
    exact ⟨tcb', hU, hW⟩

theorem updateTcbAtCode (st : SystemState) (k : Nat) {g : TCB → TCB} (hInv : st.objects.invExt)
    (hS : ∀ x, TcbWaitsKept x (g x)) (hN : ∀ x, TcbNtfnKept x (g x) := by tcb_ntfn_kept) :
    QueueLabelsFrame st (st.updateTcbAtCode k g) := by
  unfold SystemState.updateTcbAtCode
  split
  · exact refl hInv
  · exact mapTcbInPlace st _ hInv hS fun x _ => hN x

/-- **The reply-waiter link writes keep every thread's IPC state.** -/
theorem linkReplyWaiter (st : SystemState) (w s : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    QueueLabelsFrame st (st.linkReplyWaiter w s) := by
  unfold SystemState.linkReplyWaiter
  dsimp only
  have S1 := mapTcbInPlace st w hInv (g := fun x => { x with
    replyWaiterPrevCode := 0, replyWaiterNextCode := st.replyHeadCode s })
    fun _ => TcbWaitsKept.of_ipc rfl
  have S2 := S1.trans (updateTcbAtCode _ (st.replyHeadCode s) S1.invExt
    (g := fun x => { x with replyWaiterPrevCode := SeLe4n.Kernel.LinkedQueue.code w })
    fun _ => TcbWaitsKept.of_ipc rfl)
  exact S2.trans (mapTcbInPlace _ s S2.invExt fun _ => TcbWaitsKept.of_ipc rfl)

theorem unlinkReplyWaiter (st : SystemState) (w s : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    QueueLabelsFrame st (st.unlinkReplyWaiter w s) := by
  unfold SystemState.unlinkReplyWaiter
  dsimp only
  have S1 := updateTcbAtCode st (st.replyPrevCode w) hInv
    (g := fun x => { x with replyWaiterNextCode := st.replyNextCode w })
    fun _ => TcbWaitsKept.of_ipc rfl
  have S2 := S1.trans (updateTcbAtCode _ (st.replyNextCode w) S1.invExt
    (g := fun x => { x with replyWaiterPrevCode := st.replyPrevCode w })
    fun _ => TcbWaitsKept.of_ipc rfl)
  have S3 := S2.trans (mapTcbInPlace _ s S2.invExt (g := fun x => { x with
    replyWaitersHeadCode := if st.replyPrevCode w = 0 then st.replyNextCode w
      else x.replyWaitersHeadCode,
    replyWaitersCount := x.replyWaitersCount - 1 }) fun _ => TcbWaitsKept.of_ipc rfl)
  exact S3.trans (mapTcbInPlace _ w S3.invExt fun _ => TcbWaitsKept.of_ipc rfl)

theorem unlinkReplyWaiterOpt (st : SystemState) (w : SeLe4n.ThreadId) (s? : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : QueueLabelsFrame st (st.unlinkReplyWaiterOpt w s?) := by
  cases s? with
  | none => exact refl hInv
  | some s => exact unlinkReplyWaiter st w s hInv

end QueueLabelsFrame

/-- **The write that creates an endpoint waiter**: the IPC-state store of a
state waiting on `e0`, a growth at its thread and that endpoint. -/
theorem QueueLabelsGrowFrame.storeTcbIpcStateAndMessage {st st' : SystemState} {t : SeLe4n.ThreadId}
    {s : ThreadIpcState} {m : Option IpcMessage} {e0 : SeLe4n.ObjId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.storeTcbIpcStateAndMessage st t s m = .ok st')
    (hs : ∀ e, ipcWaitsOnEndpoint s e → e = e0)
    (hN : ∀ x, st.objects[t.toObjId]? = some (.tcb x) →
      TcbNtfnKept x (TCB.setIpcState { x with pendingMessage := m } s) := by tcb_ntfn_kept) :
    QueueLabelsGrowFrame t e0 st st' := by
  obtain ⟨tcb, hL, hSt⟩ := modifyTcb_ok_decompose h
  have hO := lookupTcb_some_objects st t tcb hL
  refine ⟨?_, NtfnLabelsKept.storeObject_tcb hInv hO hSt (hN tcb hO),
    storeObject_preserves_objects_invExt st st' _ _ hInv hSt⟩
  refine EndpointWaitersGrowAt.of_slot (fun k hk => storeObject_objects_ne st st' _ k _ hk hInv hSt) fun y hy e hW => ?_
  rw [storeObject_objects_eq st st' _ _ hInv hSt] at hy
  cases hy
  exact .inr (hs e (by simpa using hW))

end SeLe4n.Kernel
