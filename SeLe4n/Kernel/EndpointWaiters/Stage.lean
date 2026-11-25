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

/-! # The waiters' stage: the unit a kernel entry chains

WS-SX SX11.2 (D38).  `endpointWaitersLabelsEqual` (every thread blocked
sending, calling or receiving on an endpoint has the endpoint's label) is
carried across a kernel entry the way the kernel records are (`RecordsStage`,
`KernelRecords/Frame.lean`): each step of the entry is a `EndpointWaitersStage`, and
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

/-- **A step that carries the waiters' labels**: the unit a kernel entry chains. -/
def EndpointWaitersStage (ctx : LabelingContext) (st st' : SystemState) : Prop :=
  endpointWaitersLabelsEqual ctx st → endpointWaitersLabelsEqual ctx st'

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
theorem stage {ctx : LabelingContext} {st st' : SystemState} (h : EndpointWaitersShrink st st') :
    EndpointWaitersStage ctx st st' := fun hE => endpointWaitersLabelsEqual.of_label fun x t' e hL hW => by
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
theorem stage {ctx : LabelingContext} {st st' : SystemState} (h : EndpointWaitersGrowAt w e st st')
    (hL : ctx.threadLabelOf w = ctx.endpointLabelOf e) : EndpointWaitersStage ctx st st' :=
  fun hE => endpointWaitersLabelsEqual.of_label fun x t' e' hLk hW => by
    rcases h x t' e' (getTcb?_of_lookupTcb _ _ _ hLk) hW with ⟨t, hT, hW0⟩ | ⟨rfl, rfl⟩
    · exact hE.label (lookupTcb_of_getTcb?_of_lookupTcb hLk hT) hW0
    · exact hL

theorem of_fst_eq {α : Type} {st st' : SystemState} {p : SystemState × α} {r : α}
    (s : EndpointWaitersGrowAt w e st p.1) (h : p = (st', r)) : EndpointWaitersGrowAt w e st st' := by
  subst h; exact s

end EndpointWaitersGrowAt

namespace EndpointWaitersStage

variable {ctx : LabelingContext}

theorem refl (st : SystemState) : EndpointWaitersStage ctx st st := id

theorem trans {a b c : SystemState} (h₁ : EndpointWaitersStage ctx a b) (h₂ : EndpointWaitersStage ctx b c) :
    EndpointWaitersStage ctx a c := h₂ ∘ h₁

theorem of_eq {st st' : SystemState} (h : st' = st) : EndpointWaitersStage ctx st st' := by
  subst h; exact refl _

theorem of_frame {st st' : SystemState} (F : RecordsFrame st st') : EndpointWaitersStage ctx st st' :=
  (EndpointWaitersShrink.of_frame F).stage

theorem of_coreFrame {st st' : SystemState} (F : RecordsCoreFrame st st') :
    EndpointWaitersStage ctx st st' :=
  (EndpointWaitersShrink.of_coreFrame F).stage

theorem of_fst_eq {α : Type} {st st' : SystemState} {p : SystemState × α} {r : α}
    (s : EndpointWaitersStage ctx st p.1) (h : p = (st', r)) : EndpointWaitersStage ctx st st' := by
  subst h; exact s

end EndpointWaitersStage

/-! ### The frames: the relations with the store's invariant

A step's relation and the store's invariant at the state it reaches, which the
next step's frames read (`LendersFrame`'s shape). -/

/-- **A step that introduces no endpoint waiter**, with the store's invariant. -/
structure EndpointWaitersFrame (st st' : SystemState) : Prop where
  shrink : EndpointWaitersShrink st st'
  invExt : st'.objects.invExt

/-- **A step that blocks at most `w` on `e`**, with the store's invariant. -/
structure EndpointWaitersGrowFrame (w : SeLe4n.ThreadId) (e : SeLe4n.ObjId) (st st' : SystemState) : Prop where
  grow : EndpointWaitersGrowAt w e st st'
  invExt : st'.objects.invExt

namespace EndpointWaitersFrame

theorem refl {st : SystemState} (h : st.objects.invExt) : EndpointWaitersFrame st st := ⟨.refl _, h⟩

theorem trans {a b c : SystemState} (F : EndpointWaitersFrame a b) (G : EndpointWaitersFrame b c) :
    EndpointWaitersFrame a c := ⟨F.shrink.trans G.shrink, G.invExt⟩

theorem andThen {a b c : SystemState} (F : EndpointWaitersFrame a b)
    (G : b.objects.invExt → EndpointWaitersFrame b c) : EndpointWaitersFrame a c := F.trans (G F.invExt)

theorem of_frame {st st' : SystemState} (F : RecordsFrame st st') : EndpointWaitersFrame st st' :=
  ⟨.of_frame F, F.invExt⟩

theorem of_coreFrame {st st' : SystemState} (F : RecordsCoreFrame st st') :
    EndpointWaitersFrame st st' :=
  ⟨.of_coreFrame F, F.invExt⟩

theorem of_eq {st st' : SystemState} (hInv : st.objects.invExt) (h : st' = st) :
    EndpointWaitersFrame st st' := by subst h; exact refl hInv

theorem growAt {st st' : SystemState} (F : EndpointWaitersFrame st st') (w : SeLe4n.ThreadId)
    (e : SeLe4n.ObjId) : EndpointWaitersGrowFrame w e st st' := ⟨F.shrink.growAt w e, F.invExt⟩

/-- A frame followed by a growth is a growth. -/
theorem thenGrow {a b c : SystemState} {w : SeLe4n.ThreadId} {e : SeLe4n.ObjId}
    (F : EndpointWaitersFrame a b) (G : EndpointWaitersGrowFrame w e b c) : EndpointWaitersGrowFrame w e a c :=
  ⟨EndpointWaitersGrowAt.shrink_trans F.shrink G.grow, G.invExt⟩

theorem stage {ctx : LabelingContext} {st st' : SystemState} (F : EndpointWaitersFrame st st') :
    EndpointWaitersStage ctx st st' := F.shrink.stage

theorem of_fst_eq {α : Type} {st st' : SystemState} {p : SystemState × α} {r : α}
    (s : EndpointWaitersFrame st p.1) (h : p = (st', r)) : EndpointWaitersFrame st st' := by subst h; exact s

end EndpointWaitersFrame

namespace EndpointWaitersGrowFrame

variable {w : SeLe4n.ThreadId} {e : SeLe4n.ObjId}

theorem thenFrame {a b c : SystemState} (G : EndpointWaitersGrowFrame w e a b) (F : EndpointWaitersFrame b c) :
    EndpointWaitersGrowFrame w e a c := ⟨G.grow.trans_shrink F.shrink, F.invExt⟩

theorem andThen {a b c : SystemState} (G : EndpointWaitersGrowFrame w e a b)
    (F : b.objects.invExt → EndpointWaitersFrame b c) : EndpointWaitersGrowFrame w e a c := G.thenFrame (F G.invExt)

theorem refl {st : SystemState} (h : st.objects.invExt) : EndpointWaitersGrowFrame w e st st :=
  (EndpointWaitersFrame.refl h).growAt w e

theorem stage {ctx : LabelingContext} {st st' : SystemState} (G : EndpointWaitersGrowFrame w e st st')
    (hL : ctx.threadLabelOf w = ctx.endpointLabelOf e) : EndpointWaitersStage ctx st st' := G.grow.stage hL

theorem of_fst_eq {α : Type} {st st' : SystemState} {p : SystemState × α} {r : α}
    (s : EndpointWaitersGrowFrame w e st p.1) (h : p = (st', r)) : EndpointWaitersGrowFrame w e st st' := by
  subst h; exact s

end EndpointWaitersGrowFrame

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

namespace EndpointWaitersFrame

open EndpointWaitersShrink in
/-- **A TCB stored over a TCB**, keeping its waits. -/
theorem storeObject_tcb {st st' : SystemState} {t : SeLe4n.ThreadId} {x y : TCB}
    (hInv : st.objects.invExt) (hOld : st.objects[t.toObjId]? = some (.tcb x))
    (h : storeObject t.toObjId (.tcb y) st = .ok ((), st')) (hS : TcbWaitsKept x y) :
    EndpointWaitersFrame st st' :=
  ⟨of_slot (fun k hk => storeObject_objects_ne st st' _ k _ hk hInv h) fun y' hy e hW => by
    rw [storeObject_objects_eq st st' _ _ hInv h] at hy
    cases hy
    exact ⟨x, hOld, hS e hW⟩, storeObject_preserves_objects_invExt st st' _ _ hInv h⟩

/-- **The checked TCB write**, keeping the thread's waits. -/
theorem modifyTcb {st st' : SystemState} {t : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.modifyTcb st t f = .ok st')
    (hS : ∀ x, TcbWaitsKept x (f x)) : EndpointWaitersFrame st st' := by
  obtain ⟨tcb, hL, hSt⟩ := modifyTcb_ok_decompose h
  exact storeObject_tcb hInv (lookupTcb_some_objects st t tcb hL) hSt (hS tcb)

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
    (hInv : st.objects.invExt) (hS : ∀ x, TcbWaitsKept x (f x)) :
    EndpointWaitersFrame st (st.updateTcb t f) :=
  ⟨updateTcb_shrink st t hInv hS, SystemState.updateTcb_preserves_objects_invExt st t f hInv⟩

/-- An IPC-state and message store of a state waiting on no endpoint. -/
theorem storeTcbIpcStateAndMessage {st st' : SystemState} {t : SeLe4n.ThreadId}
    {s : ThreadIpcState} {m : Option IpcMessage} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.storeTcbIpcStateAndMessage st t s m = .ok st')
    (hs : ∀ e, ¬ ipcWaitsOnEndpoint s e := by intro e; simp) : EndpointWaitersFrame st st' :=
  modifyTcb hInv h fun _ => TcbWaitsKept.of_noWait (by simpa using hs)

theorem storeTcbIpcState {st st' : SystemState} {t : SeLe4n.ThreadId} {s : ThreadIpcState}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.storeTcbIpcState st t s = .ok st')
    (hs : ∀ e, ¬ ipcWaitsOnEndpoint s e := by intro e; simp) : EndpointWaitersFrame st st' :=
  modifyTcb hInv h fun _ => TcbWaitsKept.of_noWait (by simpa using hs)

theorem storeTcbReceiveComplete {st st' : SystemState} {t : SeLe4n.ThreadId}
    {m : Option IpcMessage} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.storeTcbReceiveComplete st t m = .ok st') : EndpointWaitersFrame st st' :=
  modifyTcb hInv h fun _ => TcbWaitsKept.of_noWait (by simp)

/-- **A thread rewritten in its slot**, keeping its waits. -/
theorem mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId) {g : TCB → TCB}
    (hInv : st.objects.invExt) (hS : ∀ x, TcbWaitsKept x (g x)) :
    EndpointWaitersFrame st (st.mapTcbInPlace t g) := by
  refine ⟨fun u tcb' e hU hW => ?_, SystemState.mapTcbInPlace_objects_invExt _ _ _ hInv⟩
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
    (hS : ∀ x, TcbWaitsKept x (g x)) : EndpointWaitersFrame st (st.updateTcbAtCode k g) := by
  unfold SystemState.updateTcbAtCode
  split
  · exact refl hInv
  · exact mapTcbInPlace st _ hInv hS

/-- **The reply-waiter link writes keep every thread's IPC state.** -/
theorem linkReplyWaiter (st : SystemState) (w s : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (st.linkReplyWaiter w s) := by
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
    EndpointWaitersFrame st (st.unlinkReplyWaiter w s) := by
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
    (hInv : st.objects.invExt) : EndpointWaitersFrame st (st.unlinkReplyWaiterOpt w s?) := by
  cases s? with
  | none => exact refl hInv
  | some s => exact unlinkReplyWaiter st w s hInv

end EndpointWaitersFrame

/-- **The write that creates an endpoint waiter**: the IPC-state store of a
state waiting on `e0`, a growth at its thread and that endpoint. -/
theorem EndpointWaitersGrowFrame.storeTcbIpcStateAndMessage {st st' : SystemState} {t : SeLe4n.ThreadId}
    {s : ThreadIpcState} {m : Option IpcMessage} {e0 : SeLe4n.ObjId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.storeTcbIpcStateAndMessage st t s m = .ok st')
    (hs : ∀ e, ipcWaitsOnEndpoint s e → e = e0) : EndpointWaitersGrowFrame t e0 st st' := by
  obtain ⟨tcb, hL, hSt⟩ := modifyTcb_ok_decompose h
  refine ⟨?_, storeObject_preserves_objects_invExt st st' _ _ hInv hSt⟩
  refine EndpointWaitersGrowAt.of_slot (fun k hk => storeObject_objects_ne st st' _ k _ hk hInv hSt) fun y hy e hW => ?_
  rw [storeObject_objects_eq st st' _ _ hInv hSt] at hy
  cases hy
  exact .inr (hs e (by simpa using hW))

end SeLe4n.Kernel
