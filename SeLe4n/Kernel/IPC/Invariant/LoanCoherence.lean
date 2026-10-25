/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Invariant.Defs
import SeLe4n.Kernel.Scheduler.RunQueueLinkFrame

/-!
# A lent scheduling context is headed by its lender's reply frame

WS-ZA ZA5.4 part 25.  seL4 MCS lends a caller's scheduling context to a
passive server in the same step that pushes the caller's reply object as that
context's reply-stack head (`donateSchedContext`, `reply_push`).  So a thread
holding a context on loan (`.donated scId owner`) always finds the lender's
reply frame heading `scId`: `lentContextHeadsLenderFrame`.  It is the
binding-to-head half of `donatedContextIsOwnerFrameHead`, read off the object
store alone, and it is what lets a final delete decide in O(1) that a
non-head reply's caller lends to no one: under it, a loan from that caller
would make the caller's frame the head.

The fact is stated, not derived — no invariant of this tree entails it (the
`docs/REGISTERED_DEBT.md` row on the stated coherence hypotheses) — so it is a
pre-state fact of the delete dispatch's pack.  What this module proves is that
the finalising delete's own steps keep it, so the delete and the revocation
loop carry it from that one pre-state fact.  The frame is `loanWrite`: every
key keeps its object, or holds a thread whose reply link is kept and whose
loan is kept or given up, or holds a reply that, if it headed a stack, still
heads it.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **Every lent scheduling context is headed by its lender's reply frame**:
a thread holding `scId` on loan from `owner` (`.donated scId owner`) finds the
lender's reply object heading `scId`'s reply stack (`next = .head scId`). -/
def lentContextHeadsLenderFrame (st : SystemState) : Prop :=
  ∀ (holder : SeLe4n.ThreadId) (ht : TCB) (scId : SeLe4n.SchedContextId)
    (owner : SeLe4n.ThreadId) (ot : TCB),
    st.objects[holder.toObjId]? = some (.tcb ht) →
    ht.schedContextBinding = .donated scId owner →
    st.objects[owner.toObjId]? = some (.tcb ot) →
    ∃ (rid : SeLe4n.ReplyId) (r : Reply), ot.replyObject = some rid ∧
      st.objects[rid.toObjId]? = some (.reply r) ∧ r.next = some (.head scId)

/-- **What the lent-context fact reads of a thread, kept**: its reply link,
and its loan — the same one, or none. -/
def TCB.loanKept (tx ty : TCB) : Prop :=
  tx.replyObjectCode = ty.replyObjectCode ∧
    ∀ (s : SeLe4n.SchedContextId) (o : SeLe4n.ThreadId),
      tx.schedContextBinding = .donated s o → ty.schedContextBinding = .donated s o

theorem TCB.loanKept.refl (t : TCB) : TCB.loanKept t t := ⟨rfl, fun _ _ h => h⟩

theorem TCB.loanKept.trans {a b c : TCB} (h₁ : TCB.loanKept a b) (h₂ : TCB.loanKept b c) :
    TCB.loanKept a c :=
  ⟨h₁.1.trans h₂.1, fun s o h => h₂.2 s o (h₁.2 s o h)⟩

/-- A thread whose binding codes are cleared gives up its loan. -/
theorem TCB.loanKept_of_bindingCleared {tx ty : TCB} (hR : tx.replyObjectCode = ty.replyObjectCode)
    (hO : tx.scBindingOwnerCode = 0) : TCB.loanKept tx ty := by
  refine ⟨hR, fun s o h => ?_⟩
  unfold TCB.schedContextBinding SchedContextBinding.ofCodes at h
  rw [hO] at h
  split at h <;> cases h

/-- **What a write keeps of one object for the lent-context fact**: a thread
it writes was a thread, its reply link and loan kept; a reply that headed a
stack still heads it. -/
def objectLoanKept (post pre : KernelObject) : Prop :=
  (∀ tx, post = .tcb tx → ∃ ty, pre = .tcb ty ∧ TCB.loanKept tx ty) ∧
  (∀ (r : Reply) (s : SeLe4n.SchedContextId), pre = .reply r → r.next = some (.head s) →
    ∃ r', post = .reply r' ∧ r'.next = some (.head s))

theorem objectLoanKept.trans {a b c : KernelObject} (h₁ : objectLoanKept a b)
    (h₂ : objectLoanKept b c) : objectLoanKept a c := by
  refine ⟨fun tx hx => ?_, fun r s hr hn => ?_⟩
  · obtain ⟨tb, hb, k₁⟩ := h₁.1 tx hx
    obtain ⟨tc, hc, k₂⟩ := h₂.1 tb hb
    exact ⟨tc, hc, k₁.trans k₂⟩
  · obtain ⟨rb, hb, nb⟩ := h₂.2 r s hr hn
    exact h₁.2 rb s hb nb

/-- A thread rewritten keeping its reply link and loan. -/
theorem objectLoanKept_tcb {tx ty : TCB} (h : TCB.loanKept tx ty) :
    objectLoanKept (.tcb tx) (.tcb ty) :=
  ⟨fun _ e => by cases e; exact ⟨ty, rfl, h⟩, fun _ _ e => by cases e⟩

/-- An object that is neither a thread nor a reply, rewritten as one that is
neither. -/
theorem objectLoanKept_of_inert {post pre : KernelObject}
    (hPost : ∀ t, post ≠ .tcb t) (hPre : ∀ r, pre ≠ .reply r) : objectLoanKept post pre :=
  ⟨fun t e => absurd e (hPost t), fun r _ e => absurd e (hPre r)⟩

/-- **The lent-context frame**: every key keeps its object, or holds one whose
write keeps what the lent-context fact reads (`objectLoanKept`). -/
def loanWrite (st st' : SystemState) : Prop :=
  ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
    ∃ pre post : KernelObject, st.objects[oid]? = some pre ∧ st'.objects[oid]? = some post ∧
      objectLoanKept post pre

namespace loanWrite

theorem refl (st : SystemState) : loanWrite st st := fun _ => Or.inl rfl

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) : loanWrite st st' :=
  fun _ => Or.inl (by rw [h])

theorem trans {a b c : SystemState} (h₁ : loanWrite a b) (h₂ : loanWrite b c) :
    loanWrite a c := by
  intro oid
  rcases h₁ oid with e₁ | ⟨p₁, q₁, hp₁, hq₁, k₁⟩
  · rcases h₂ oid with e₂ | ⟨p₂, q₂, hp₂, hq₂, k₂⟩
    · exact Or.inl (e₂.trans e₁)
    · exact Or.inr ⟨p₂, q₂, e₁ ▸ hp₂, hq₂, k₂⟩
  · rcases h₂ oid with e₂ | ⟨p₂, q₂, hp₂, hq₂, k₂⟩
    · exact Or.inr ⟨p₁, q₁, hp₁, e₂.trans hq₁, k₁⟩
    · rw [hq₁] at hp₂
      cases hp₂
      exact Or.inr ⟨p₁, q₂, hp₁, hq₂, k₂.trans k₁⟩

/-- One key rewritten in its slot, keeping what the fact reads. -/
theorem of_insert {st st' : SystemState} {k : SeLe4n.ObjId} {o o' : KernelObject}
    (hInv : st.objects.invExt) (hO : st'.objects = st.objects.insert k o')
    (hPre : st.objects[k]? = some o) (hK : objectLoanKept o' o) : loanWrite st st' := by
  intro oid
  rw [hO]
  by_cases e : oid = k
  · subst e
    exact Or.inr ⟨o, o', hPre, RobinHood.RHTable.getElem?_insert_self st.objects oid o' hInv, hK⟩
  · exact Or.inl (RobinHood.RHTable.getElem?_insert_ne st.objects k oid o'
      (by intro h; exact e (eq_of_beq h).symm) hInv)

/-- **Writes off the run-queue links keep it**: a thread's reply link and
binding are no run-queue link, and every other object is kept. -/
theorem of_agreeOffRunLinks {st st' : SystemState} (h : st'.objectsAgreeOffRunLinks st) :
    loanWrite st st' := by
  intro oid
  rcases h.pointwise oid with e | ⟨t, t', ht, ht'⟩
  · exact Or.inl e
  · obtain ⟨t'', ht'', hE⟩ := h.get_tcb ht
    rw [ht'] at ht''
    cases ht''
    refine Or.inr ⟨.tcb t, .tcb t', ht, ht', objectLoanKept_tcb ⟨?_, fun s o hb => ?_⟩⟩
    · exact TCB.proj_eq_of_withoutRunLinks_eq (·.replyObjectCode) hE
    · rw [← TCB.proj_eq_of_withoutRunLinks_eq (·.schedContextBinding) hE]; exact hb

end loanWrite

/-- **A state that lends no context satisfies the fact vacuously.** -/
theorem lentContextHeadsLenderFrame.of_no_loans {st : SystemState}
    (h : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
      (owner : SeLe4n.ThreadId), st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.schedContextBinding ≠ .donated scId owner) :
    lentContextHeadsLenderFrame st :=
  fun holder ht scId owner _ hH hB _ => absurd hB (h holder ht scId owner hH)

/-- **The lent-context fact survives a lent-context frame.** -/
theorem lentContextHeadsLenderFrame.of_loanWrite {st st' : SystemState}
    (h : lentContextHeadsLenderFrame st) (F : loanWrite st st') :
    lentContextHeadsLenderFrame st' := by
  have back : ∀ (k : SeLe4n.ObjId) (tx : TCB), st'.objects[k]? = some (.tcb tx) →
      ∃ ty, st.objects[k]? = some (.tcb ty) ∧ TCB.loanKept tx ty := by
    intro k tx hx
    rcases F k with e | ⟨pre, post, hp, hq, hK⟩
    · exact ⟨tx, e ▸ hx, TCB.loanKept.refl tx⟩
    · rw [hq] at hx; cases hx
      obtain ⟨ty, rfl, hk⟩ := hK.1 tx rfl
      exact ⟨ty, hp, hk⟩
  intro holder hx scId owner ox hH hB hO
  obtain ⟨hy, hHy, kH⟩ := back _ hx hH
  obtain ⟨oy, hOy, kO⟩ := back _ ox hO
  obtain ⟨rid, r, hRO, hR, hN⟩ := h holder hy scId owner oy hHy (kH.2 scId owner hB) hOy
  have hRO' : ox.replyObject = some rid := by
    unfold TCB.replyObject at hRO ⊢; rw [kO.1]; exact hRO
  rcases F rid.toObjId with e | ⟨pre, post, hp, hq, hK⟩
  · exact ⟨rid, r, hRO', e ▸ hR, hN⟩
  · rw [hR] at hp; cases hp
    obtain ⟨r', rfl, hN'⟩ := hK.2 r scId rfl hN
    exact ⟨rid, r', hRO', hq, hN'⟩

/-! ### One thread's reply link let go

A finalised reply's caller gives up its reply link (`consumeCallerReply`), so
the frame that keeps every thread's link is too strong for that step.  The
lent-context fact still survives it when the caller lends to no one: no loan
reads that thread's link. -/

/-- **What the lent-context fact reads of a thread, kept, its reply link
perhaps not** (`free`): its loan — the same one, or none. -/
def TCB.loanKeptOff (free : Prop) (tx ty : TCB) : Prop :=
  (free ∨ tx.replyObjectCode = ty.replyObjectCode) ∧
    ∀ (s : SeLe4n.SchedContextId) (o : SeLe4n.ThreadId),
      tx.schedContextBinding = .donated s o → ty.schedContextBinding = .donated s o

/-- **`objectLoanKept`, a thread's reply link perhaps let go** (`free`). -/
def objectLoanKeptOff (free : Prop) (post pre : KernelObject) : Prop :=
  (∀ tx, post = .tcb tx → ∃ ty, pre = .tcb ty ∧ TCB.loanKeptOff free tx ty) ∧
  (∀ (r : Reply) (s : SeLe4n.SchedContextId), pre = .reply r → r.next = some (.head s) →
    ∃ r', post = .reply r' ∧ r'.next = some (.head s))

theorem objectLoanKept.off {post pre : KernelObject} (free : Prop) (h : objectLoanKept post pre) :
    objectLoanKeptOff free post pre := by
  refine ⟨fun tx hx => ?_, h.2⟩
  obtain ⟨ty, hy, k⟩ := h.1 tx hx
  exact ⟨ty, hy, Or.inr k.1, k.2⟩

theorem objectLoanKeptOff.trans {free : Prop} {a b c : KernelObject}
    (h₁ : objectLoanKeptOff free a b) (h₂ : objectLoanKeptOff free b c) :
    objectLoanKeptOff free a c := by
  refine ⟨fun tx hx => ?_, fun r s hr hn => ?_⟩
  · obtain ⟨tb, hb, k₁⟩ := h₁.1 tx hx
    obtain ⟨tc, hc, k₂⟩ := h₂.1 tb hb
    refine ⟨tc, hc, ?_, fun s o h => k₂.2 s o (k₁.2 s o h)⟩
    rcases k₁.1 with f | e₁
    · exact Or.inl f
    · rcases k₂.1 with f | e₂
      · exact Or.inl f
      · exact Or.inr (e₁.trans e₂)
  · obtain ⟨rb, hb, nb⟩ := h₂.2 r s hr hn
    exact h₁.2 rb s hb nb

/-- **The lent-context frame, the thread `c`'s reply link let go.** -/
def loanWriteOff (c : SeLe4n.ThreadId) (st st' : SystemState) : Prop :=
  ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
    ∃ pre post : KernelObject, st.objects[oid]? = some pre ∧ st'.objects[oid]? = some post ∧
      objectLoanKeptOff (oid = c.toObjId) post pre

theorem loanWrite.off {st st' : SystemState} (c : SeLe4n.ThreadId) (h : loanWrite st st') :
    loanWriteOff c st st' := by
  intro oid
  rcases h oid with e | ⟨pre, post, hp, hq, k⟩
  · exact Or.inl e
  · exact Or.inr ⟨pre, post, hp, hq, k.off _⟩

theorem loanWriteOff.trans {c : SeLe4n.ThreadId} {a b d : SystemState}
    (h₁ : loanWriteOff c a b) (h₂ : loanWriteOff c b d) : loanWriteOff c a d := by
  intro oid
  rcases h₁ oid with e₁ | ⟨p₁, q₁, hp₁, hq₁, k₁⟩
  · rcases h₂ oid with e₂ | ⟨p₂, q₂, hp₂, hq₂, k₂⟩
    · exact Or.inl (e₂.trans e₁)
    · exact Or.inr ⟨p₂, q₂, e₁ ▸ hp₂, hq₂, k₂⟩
  · rcases h₂ oid with e₂ | ⟨p₂, q₂, hp₂, hq₂, k₂⟩
    · exact Or.inr ⟨p₁, q₁, hp₁, e₂.trans hq₁, k₁⟩
    · rw [hq₁] at hp₂
      cases hp₂
      exact Or.inr ⟨p₁, q₂, hp₁, hq₂, k₂.trans k₁⟩

/-- One key rewritten in its slot, keeping what the fact reads, `c`'s reply
link perhaps not. -/
theorem loanWriteOff.of_insert {c : SeLe4n.ThreadId} {st st' : SystemState} {k : SeLe4n.ObjId}
    {o o' : KernelObject} (hInv : st.objects.invExt) (hO : st'.objects = st.objects.insert k o')
    (hPre : st.objects[k]? = some o) (hK : objectLoanKeptOff (k = c.toObjId) o' o) :
    loanWriteOff c st st' := by
  intro oid
  rw [hO]
  by_cases e : oid = k
  · subst e
    exact Or.inr ⟨o, o', hPre, RobinHood.RHTable.getElem?_insert_self st.objects oid o' hInv, hK⟩
  · exact Or.inl (RobinHood.RHTable.getElem?_insert_ne st.objects k oid o'
      (by intro h; exact e (eq_of_beq h).symm) hInv)

/-- **The lent-context fact survives a frame that lets go of the reply link of
a thread that lends to no one.** -/
theorem lentContextHeadsLenderFrame.of_loanWriteOff {c : SeLe4n.ThreadId} {st st' : SystemState}
    (h : lentContextHeadsLenderFrame st)
    (hNo : ∀ (holder : SeLe4n.ThreadId) (ht : TCB) (s : SeLe4n.SchedContextId),
      st.objects[holder.toObjId]? = some (.tcb ht) → ht.schedContextBinding ≠ .donated s c)
    (F : loanWriteOff c st st') : lentContextHeadsLenderFrame st' := by
  have back : ∀ (k : SeLe4n.ObjId) (tx : TCB), st'.objects[k]? = some (.tcb tx) →
      ∃ ty, st.objects[k]? = some (.tcb ty) ∧ TCB.loanKeptOff (k = c.toObjId) tx ty := by
    intro k tx hx
    rcases F k with e | ⟨pre, post, hp, hq, hK⟩
    · exact ⟨tx, e ▸ hx, Or.inr rfl, fun _ _ h => h⟩
    · rw [hq] at hx; cases hx
      obtain ⟨ty, rfl, hk⟩ := hK.1 tx rfl
      exact ⟨ty, hp, hk⟩
  intro holder hx scId owner ox hH hB hO
  obtain ⟨hy, hHy, kH⟩ := back _ hx hH
  obtain ⟨oy, hOy, kO⟩ := back _ ox hO
  have hBy := kH.2 scId owner hB
  have hRC : ox.replyObjectCode = oy.replyObjectCode := by
    rcases kO.1 with f | e
    · exact (hNo holder hy scId hHy (by rw [← SeLe4n.ThreadId.toObjId_injective _ _ f]; exact hBy)).elim
    · exact e
  obtain ⟨rid, r, hRO, hR, hN⟩ := h holder hy scId owner oy hHy hBy hOy
  have hRO' : ox.replyObject = some rid := by
    unfold TCB.replyObject at hRO ⊢; rw [hRC]; exact hRO
  rcases F rid.toObjId with e | ⟨pre, post, hp, hq, hK⟩
  · exact ⟨rid, r, hRO', e ▸ hR, hN⟩
  · rw [hR] at hp; cases hp
    obtain ⟨r', rfl, hN'⟩ := hK.2 r scId rfl hN
    exact ⟨rid, r', hRO', hq, hN'⟩

end SeLe4n.Kernel
