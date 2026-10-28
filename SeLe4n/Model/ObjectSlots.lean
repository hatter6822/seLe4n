-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.Object.DerivationLinks

/-!
# The capability slots of an object

Two kinds of object hold capability slots: a CNode (its slot array,
`CNode.cells`, and their link words, `CNode.links`) and a thread (its CSpace and
VSpace root slots, `TCB.spaceCells`, and their link words, `TCB.spaceLinks`, as
seL4's `tcbCTable` and `tcbVTable`).  The readers and writers here dispatch on
the object's kind: the `.cnode` arm is the CNode's own function, so every CNode
theorem is reused, and the `.tcb` arm reads and writes the thread's two slots,
indices 0 and 1.  Any other index of a thread, and any slot of any other kind
of object, is no slot.
-/

namespace SeLe4n.Model

namespace TCB

/-- The capability a thread's space slot `s` holds; slots 0 and 1 only.  Out
of line, so its bound check is no branch of its caller. -/
@[noinline] def spaceSlotCap (t : TCB) (s : SeLe4n.Slot) : Option Capability :=
  if h : s.toNat < 2 then t.spaceCells[s.toNat] else none

/-- The cell of slot `s` of a thread's space cells, read from the cells alone
(`spaceCellAt_eq`).  Out of line and taking only the cells, so a caller that
rebuilds the thread after reading a slot (`removeSpaceCapImpl`) hands the
thread to no call and rebuilds it over the old thread's cell when that is
unshared. -/
@[noinline] def spaceCellAt (cells : Vector (Option Capability) 2) (s : SeLe4n.Slot) :
    Option Capability :=
  if h : s.toNat < 2 then cells[s.toNat] else none

theorem spaceCellAt_eq (t : TCB) (s : SeLe4n.Slot) :
    spaceCellAt t.spaceCells s = t.spaceSlotCap s := rfl

/-- The object word of link `f` of the thread's space slot `s` (0 past slot 1). -/
@[inline] def spaceLinkNodeWord (t : TCB) (s : SeLe4n.Slot) (f : LinkField) : Nat :=
  t.spaceLinks.toArray.getD (CNode.linkBase s f) 0

/-- The slot word of link `f` of the thread's space slot `s`. -/
@[inline] def spaceLinkSlotWord (t : TCB) (s : SeLe4n.Slot) (f : LinkField) : Nat :=
  t.spaceLinks.toArray.getD (CNode.linkBase s f + 1) 0

/-- Link `f` of the thread's space slot `s`, decoded from its two words. -/
def spaceLinkAt (t : TCB) (s : SeLe4n.Slot) (f : LinkField) : Option SlotRef :=
  decodeLink (t.spaceLinkNodeWord s f) (t.spaceLinkSlotWord s f)

/-- Write link `f` of the thread's space slot `s` in place, as its two words. -/
@[inline] def setSpaceLinkWords (t : TCB) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) : TCB :=
  { t with spaceLinks :=
      (t.spaceLinks.setIfInBounds (CNode.linkBase s f) c).setIfInBounds (CNode.linkBase s f + 1) w }

/-- A space-slot link write keeps the thread's taint words. -/
@[simp] theorem setSpaceLinkWords_taintWords (t : TCB) (s : SeLe4n.Slot) (f : LinkField)
    (c w : Nat) : (t.setSpaceLinkWords s f c w).taintWords = t.taintWords := rfl

/-- The thread with every space-slot link cleared.  The information-flow
projection reads a thread through this, so the links, like the derivation tree
they encode, are never observable. -/
def withoutLinks (t : TCB) : TCB :=
  { t with spaceLinks := Vector.replicate _ 0 }

/-- The thread with its space slot `s` emptied (the identity past slot 1). -/
@[inline] def removeSpaceCap (t : TCB) (s : SeLe4n.Slot) : TCB :=
  { t with spaceCells := t.spaceCells.setIfInBounds s.toNat none }

/-- The thread with its space slot `s` holding `cap` (the identity past slot 1). -/
@[inline] def insertSpaceCap (t : TCB) (s : SeLe4n.Slot) (cap : Capability) : TCB :=
  { t with spaceCells := t.spaceCells.setIfInBounds s.toNat (some cap) }

/-- WS-ZA ZA5.4 part 26: `removeSpaceCap` as compiled: the slot's cell, read
before the slot is written, is kept as the slot's spare record
(`TCB.spaceSpare`, `SpareCells.keep`), so the next capability written there
overwrites it in place (`removeSpaceCap_eq_impl`). -/
@[inline] def removeSpaceCapImpl (t : TCB) (s : SeLe4n.Slot) : TCB :=
  let o := spaceCellAt t.spaceCells s
  { t with
    spaceCells := t.spaceCells.setIfInBounds s.toNat none
    spaceSpare := t.spaceSpare.keep s.toNat o }

@[csimp] theorem removeSpaceCap_eq_impl : @removeSpaceCap = @removeSpaceCapImpl := by
  funext t s
  exact (TCB.with_spaceSpare (t.removeSpaceCap s) _).symm

@[simp] theorem withoutLinks_spaceCells (t : TCB) : t.withoutLinks.spaceCells = t.spaceCells := rfl
@[simp] theorem withoutLinks_withoutLinks (t : TCB) : t.withoutLinks.withoutLinks = t.withoutLinks := rfl
@[simp] theorem setSpaceLinkWords_spaceCells (t : TCB) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
    (t.setSpaceLinkWords s f c w).spaceCells = t.spaceCells := rfl
@[simp] theorem withoutLinks_setSpaceLinkWords (t : TCB) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
    (t.setSpaceLinkWords s f c w).withoutLinks = t.withoutLinks := rfl
@[simp] theorem spaceSlotCap_withoutLinks (t : TCB) (s : SeLe4n.Slot) :
    t.withoutLinks.spaceSlotCap s = t.spaceSlotCap s := rfl
@[simp] theorem cspaceRoot_withoutLinks (t : TCB) : t.withoutLinks.cspaceRoot = t.cspaceRoot := rfl
@[simp] theorem vspaceRoot_withoutLinks (t : TCB) : t.withoutLinks.vspaceRoot = t.vspaceRoot := rfl

/-- The capabilities the thread's space slots hold, with their slots. -/
def spaceSlotCaps (t : TCB) : List (SeLe4n.Slot × Capability) :=
  [(cspaceRootSlot, t.spaceCells[0]), (vspaceRootSlot, t.spaceCells[1])].filterMap
    fun p => p.2.map (p.1, ·)

/-- **Every space-slot link word is 0**: the thread's slots hold no derivation
link.  The boot check reads it, as it reads `CNode.linksClear`. -/
def spaceLinksClear (t : TCB) : Bool := t.spaceLinks.toList.all (· == 0)

theorem spaceLinkAt_of_spaceLinksClear {t : TCB} (h : t.spaceLinksClear = true)
    (s : SeLe4n.Slot) (f : LinkField) : t.spaceLinkAt s f = none := by
  have hz : t.spaceLinkNodeWord s f = 0 := by
    unfold spaceLinkNodeWord
    rw [Array.getD_eq_getD_getElem?]
    cases hi : t.spaceLinks.toArray[CNode.linkBase s f]? with
    | none => rfl
    | some v =>
      have hm : v ∈ t.spaceLinks.toArray := Array.mem_of_getElem? hi
      have := (List.all_eq_true.mp h) v (by
        rw [Vector.toList]; exact Array.mem_def.mp hm)
      simpa using this
  unfold spaceLinkAt decodeLink; rw [hz]; rfl

/-- A capability a space slot holds is listed by `spaceSlotCaps`. -/
theorem mem_spaceSlotCaps {t : TCB} {s : SeLe4n.Slot} {cap : Capability}
    (h : t.spaceSlotCap s = some cap) : ∃ s', (s', cap) ∈ t.spaceSlotCaps := by
  unfold spaceSlotCap at h
  split at h
  · next hs =>
    unfold spaceSlotCaps
    have : s.toNat = 0 ∨ s.toNat = 1 := by omega
    rcases this with e | e
    · refine ⟨cspaceRootSlot, List.mem_filterMap.mpr ⟨(cspaceRootSlot, t.spaceCells[0]), by simp, ?_⟩⟩
      simp only [e] at h; simp [h]
    · refine ⟨vspaceRootSlot, List.mem_filterMap.mpr ⟨(vspaceRootSlot, t.spaceCells[1]), by simp, ?_⟩⟩
      simp only [e] at h; simp [h]
  · cases h

/-- Two threads that agree off their space-slot links agree on anything that
reads past those links. -/
@[elab_without_expected_type]
theorem proj_eq_of_withoutLinks_eq {α : Sort _} {a b : TCB} (f : TCB → α)
    (h : a.withoutLinks = b.withoutLinks)
    (hf : ∀ c : TCB, f c.withoutLinks = f c := by intro; rfl) : f a = f b := by
  rw [← hf a, ← hf b, h]

/-- A property that reads past the space-slot links carries between two
threads that agree off them: the transport a frame that may rewrite a thread's
links (a slot write splicing a neighbour) gives its consumers. -/
@[elab_as_elim]
theorem of_withoutLinks_eq {P : TCB → Prop} {a b : TCB} (h : a.withoutLinks = b.withoutLinks)
    (hP : ∀ c : TCB, P c.withoutLinks ↔ P c) (hb : P b) : P a :=
  (hP a).mp (h ▸ (hP b).mpr hb)

/-- Two optional threads that agree off their links, present or absent: a
present one has a partner. -/
theorem exists_of_map_withoutLinks_eq {o o' : Option TCB}
    (h : o'.map withoutLinks = o.map withoutLinks) {t' : TCB} (ht : o' = some t') :
    ∃ t, o = some t ∧ t'.withoutLinks = t.withoutLinks := by
  subst ht
  cases o with
  | none => cases h
  | some t => exact ⟨t, rfl, Option.some.inj h⟩

/-- ...they are present together. -/
theorem isSome_of_map_withoutLinks_eq {o o' : Option TCB}
    (h : o'.map withoutLinks = o.map withoutLinks) : o'.isSome = o.isSome := by
  have := congrArg Option.isSome h
  simpa only [Option.isSome_map] using this

/-- ...and agree on anything that reads past the links. -/
theorem map_proj_of_map_withoutLinks_eq {α : Sort _} {o o' : Option TCB} (f : TCB → α)
    (h : o'.map withoutLinks = o.map withoutLinks)
    (hf : ∀ c : TCB, f c.withoutLinks = f c := by intro; rfl) : o'.map f = o.map f := by
  cases o' with
  | none => cases o with
    | none => rfl
    | some _ => cases h
  | some t' =>
    obtain ⟨t, rfl, hw⟩ := exists_of_map_withoutLinks_eq h rfl
    exact congrArg some (proj_eq_of_withoutLinks_eq f hw hf)

/-- **Writing a link's words** sets that link, for one of the thread's two
slots, and leaves every other link. -/
theorem spaceLinkAt_setSpaceLinkWords (t : TCB) {s : SeLe4n.Slot} (hs : s.toNat < 2)
    (f : LinkField) (c w : Nat) (s' : SeLe4n.Slot) (f' : LinkField) :
    (t.setSpaceLinkWords s f c w).spaceLinkAt s' f' =
      if s' = s ∧ f' = f then decodeLink c w else t.spaceLinkAt s' f' := by
  have hb : CNode.linkBase s f + 1 < t.spaceLinks.toArray.size := by
    rw [Vector.size_toArray]
    unfold CNode.linkBase slotLinkWords
    cases f <;> simp only [LinkField.offset] <;> omega
  unfold spaceLinkAt spaceLinkNodeWord spaceLinkSlotWord setSpaceLinkWords
  simp only [Vector.toArray_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
  by_cases he : s' = s ∧ f' = f
  · obtain ⟨rfl, rfl⟩ := he
    have hne : CNode.linkBase s' f' + 1 ≠ CNode.linkBase s' f' := Nat.succ_ne_self _
    simp only [hb, Nat.lt_of_succ_lt hb, if_true, hne, if_false, Option.getD_some, and_self]
  · have ⟨n1, n2, n3, n4⟩ := CNode.linkBase_ne he
    simp only [n1, n2, n3, n4, if_false, he]

/-- A thread's links past its two slots read as none. -/
theorem spaceLinkAt_of_ge (t : TCB) {s : SeLe4n.Slot} (hs : 2 ≤ s.toNat) (f : LinkField) :
    t.spaceLinkAt s f = none := by
  have : t.spaceLinks.toArray.size ≤ CNode.linkBase s f := by
    rw [Vector.size_toArray]; unfold CNode.linkBase slotLinkWords; omega
  unfold spaceLinkAt spaceLinkNodeWord decodeLink
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none this]; rfl

/-- **Emptying a space slot** empties that slot and leaves the other. -/
theorem spaceSlotCap_removeSpaceCap (t : TCB) (s s' : SeLe4n.Slot) :
    (t.removeSpaceCap s).spaceSlotCap s' = if s' = s then none else t.spaceSlotCap s' := by
  unfold spaceSlotCap removeSpaceCap
  by_cases he : s' = s
  · subst he
    simp only [if_true]
    split
    · next hs => simp
    · rfl
  · simp only [he, if_false]
    split
    · next hs =>
      have hn : s.toNat ≠ s'.toNat := fun h => he (SeLe4n.Slot.ext h.symm)
      simp [hn]
    · rfl

@[simp] theorem removeSpaceCap_spaceLinks (t : TCB) (s : SeLe4n.Slot) :
    (t.removeSpaceCap s).spaceLinks = t.spaceLinks := rfl

/-- A thread whose slot `s` is emptied holds no capability its record did not. -/
theorem spaceSlotCap_removeSpaceCap_back {t : TCB} {s s' : SeLe4n.Slot} {cap : Capability}
    (h : (t.removeSpaceCap s).spaceSlotCap s' = some cap) : t.spaceSlotCap s' = some cap := by
  rw [spaceSlotCap_removeSpaceCap] at h
  split at h
  · cases h
  · exact h

/-- **Filling a space slot** fills that slot, one of the thread's two, and
leaves the other. -/
theorem spaceSlotCap_insertSpaceCap (t : TCB) {s : SeLe4n.Slot} (hs : s.toNat < 2)
    (cap : Capability) (s' : SeLe4n.Slot) :
    (t.insertSpaceCap s cap).spaceSlotCap s' = if s' = s then some cap else t.spaceSlotCap s' := by
  unfold spaceSlotCap insertSpaceCap
  by_cases he : s' = s
  · subst he
    simp [hs]
  · simp only [he, if_false]
    split
    · next hs' =>
      have hn : s.toNat ≠ s'.toNat := fun h => he (SeLe4n.Slot.ext h.symm)
      simp [hn]
    · rfl

/-- A filled slot's thread holds the capability put in, or one its record held. -/
theorem spaceSlotCap_insertSpaceCap_back {t : TCB} {s s' : SeLe4n.Slot} {cap c : Capability}
    (h : (t.insertSpaceCap s cap).spaceSlotCap s' = some c) :
    c = cap ∨ t.spaceSlotCap s' = some c := by
  by_cases hs : s.toNat < 2
  · rw [spaceSlotCap_insertSpaceCap t hs] at h
    split at h
    · cases h; exact .inl rfl
    · exact .inr h
  · right
    unfold spaceSlotCap insertSpaceCap at *
    have : t.spaceCells.setIfInBounds s.toNat (some cap) = t.spaceCells := by
      apply Vector.ext; intro i hi
      simp only [Vector.getElem_setIfInBounds]
      split <;> first | omega | rfl
    simp only [this] at h
    exact h

@[simp] theorem insertSpaceCap_spaceLinks (t : TCB) (s : SeLe4n.Slot) (cap : Capability) :
    (t.insertSpaceCap s cap).spaceLinks = t.spaceLinks := rfl

/-- A filled slot holds every capability its record held, and the one put in. -/
theorem spaceSlotCap_insertSpaceCap_mono (t : TCB) {s : SeLe4n.Slot} (hs : s.toNat < 2)
    (cap : Capability) (s' : SeLe4n.Slot) (h : t.spaceSlotCap s' ≠ none) :
    (t.insertSpaceCap s cap).spaceSlotCap s' ≠ none := by
  rw [spaceSlotCap_insertSpaceCap t hs]
  split
  · simp
  · exact h

/-- **The capability a thread's space slot holds when set from `cap`**: `cap`'s
target, its rights masked by the slot's own (`rights`), with no badge and no
mapping record.  A derivation of `cap`, as seL4's `deriveCap` is: it never
carries a right `cap` lacks. -/
@[inline] def spaceCopyOf (cap : Capability) (rights : AccessRightSet) : Capability :=
  ⟨cap.target, cap.rights.inter rights, SeLe4n.Badge.zero, false, default, default, 0, false, 0⟩

@[simp] theorem spaceCopyOf_target (cap : Capability) (rights : AccessRightSet) :
    (spaceCopyOf cap rights).target = cap.target := rfl

@[simp] theorem spaceCopyOf_badge (cap : Capability) (rights : AccessRightSet) :
    (spaceCopyOf cap rights).badge = none := rfl

end TCB

namespace KernelObject

/-- **The capability slot `s` of an object holds**: a CNode's slot, a thread's
space slot, nothing for any other object. -/
@[inline] def slotCap (o : KernelObject) (s : SeLe4n.Slot) : Option Capability :=
  match o with
  | .cnode cn => cn.lookup s
  | .tcb t => t.spaceSlotCap s
  | _ => none

/-- `s` is a slot of the object: below a CNode's slot count, or one of a
thread's two space slots. -/
def hasSlot (o : KernelObject) (s : SeLe4n.Slot) : Prop :=
  match o with
  | .cnode cn => s.toNat < 2 ^ cn.radixWidth
  | .tcb _ => s.toNat < 2
  | _ => False

/-- The object word of link `f` of slot `s` (0 when it has no target). -/
@[inline] def linkNodeWord (o : KernelObject) (s : SeLe4n.Slot) (f : LinkField) : Nat :=
  match o with
  | .cnode cn => cn.linkNodeWord s f
  | .tcb t => t.spaceLinkNodeWord s f
  | _ => 0

/-- The slot word of link `f` of slot `s`. -/
@[inline] def linkSlotWord (o : KernelObject) (s : SeLe4n.Slot) (f : LinkField) : Nat :=
  match o with
  | .cnode cn => cn.linkSlotWord s f
  | .tcb t => t.spaceLinkSlotWord s f
  | _ => 0

/-- Link `f` of slot `s`; none for an object with no slots. -/
def linkAt (o : KernelObject) (s : SeLe4n.Slot) (f : LinkField) : Option SlotRef :=
  match o with
  | .cnode cn => cn.linkAt s f
  | .tcb t => t.spaceLinkAt s f
  | _ => none

/-- Write link `f` of slot `s` as its two words; the identity on an object with
no slots. -/
@[inline] def setLinkWords (o : KernelObject) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
    KernelObject :=
  match o with
  | .cnode cn => .cnode (cn.setLinkWords s f c w)
  | .tcb t => .tcb (t.setSpaceLinkWords s f c w)
  | o => o

/-- Empty slot `s`; the identity on an object with no slots. -/
@[inline] def removeSlotCap (o : KernelObject) (s : SeLe4n.Slot) : KernelObject :=
  match o with
  | .cnode cn => .cnode (cn.remove s)
  | .tcb t => .tcb (t.removeSpaceCap s)
  | o => o

theorem linkAt_eq_decode (o : KernelObject) (s : SeLe4n.Slot) (f : LinkField) :
    o.linkAt s f = decodeLink (o.linkNodeWord s f) (o.linkSlotWord s f) := by
  cases o <;> rfl

@[simp] theorem slotCap_cnode (cn : CNode) (s : SeLe4n.Slot) :
    (KernelObject.cnode cn).slotCap s = cn.lookup s := rfl
@[simp] theorem slotCap_tcb (t : TCB) (s : SeLe4n.Slot) :
    (KernelObject.tcb t).slotCap s = t.spaceSlotCap s := rfl

/-- A slot holding a capability is a slot of its object. -/
theorem hasSlot_of_slotCap {o : KernelObject} {s : SeLe4n.Slot} (h : o.slotCap s ≠ none) :
    o.hasSlot s := by
  cases o
  case cnode cn =>
    obtain ⟨cap, hCap⟩ := Option.ne_none_iff_exists'.mp h
    have := (CNode.slotAddressable_iff_lt_cells cn s).mp (CNode.slotAddressable_of_lookup cn s cap hCap)
    rw [cn.cells_size] at this; exact this
  case tcb t =>
    show s.toNat < 2
    if hs : s.toNat < 2 then exact hs
    else exact absurd (by simp only [slotCap, TCB.spaceSlotCap, hs, dite_false]) h
  all_goals exact absurd rfl h

/-- **Writing a link's words** sets that link, for a slot of the object, and
leaves every other link. -/
theorem linkAt_setLinkWords {o : KernelObject} {s : SeLe4n.Slot} (hs : o.hasSlot s)
    (f : LinkField) (c w : Nat) (s' : SeLe4n.Slot) (f' : LinkField) :
    (o.setLinkWords s f c w).linkAt s' f' =
      if s' = s ∧ f' = f then decodeLink c w else o.linkAt s' f' := by
  cases o with
  | cnode cn => exact cn.linkAt_setLinkWords hs f c w s' f'
  | tcb t => exact t.spaceLinkAt_setSpaceLinkWords hs f c w s' f'
  | _ => exact absurd hs id

/-- The object holds capability slots: a CNode or a thread. -/
@[inline] def holdsSlots (o : KernelObject) : Bool :=
  match o with
  | .cnode _ => true
  | .tcb _ => true
  | _ => false

/-- The object's link words: a CNode's `links`, a thread's `spaceLinks`; none
for any other object.  Every link read is a read of these words at the slot's
`CNode.linkBase` (`linkAt_eq_linkWords`). -/
def linkWords (o : KernelObject) : Array Nat :=
  match o with
  | .cnode cn => cn.links
  | .tcb t => t.spaceLinks.toArray
  | _ => #[]

theorem linkAt_eq_linkWords (o : KernelObject) (s : SeLe4n.Slot) (f : LinkField) :
    o.linkAt s f = decodeLink (o.linkWords.getD (CNode.linkBase s f) 0)
      (o.linkWords.getD (CNode.linkBase s f + 1) 0) := by
  cases o <;> rfl

theorem linkNodeWord_eq_linkWords (o : KernelObject) (s : SeLe4n.Slot) (f : LinkField) :
    o.linkNodeWord s f = o.linkWords.getD (CNode.linkBase s f) 0 := by
  cases o <;> rfl

theorem linkSlotWord_eq_linkWords (o : KernelObject) (s : SeLe4n.Slot) (f : LinkField) :
    o.linkSlotWord s f = o.linkWords.getD (CNode.linkBase s f + 1) 0 := by
  cases o <;> rfl

/-- The object with every derivation link cleared (a CNode's, a thread's); any
other object as it is. -/
def withoutLinks (o : KernelObject) : KernelObject :=
  match o with
  | .cnode cn => .cnode cn.withoutLinks
  | .tcb t => .tcb t.withoutLinks
  | o => o

/-- A thread's space slots and their links; none for any other object.  The
part of a thread the capability invariants read. -/
def tcbSlots (o : KernelObject) : Option (Vector (Option Capability) 2 × Vector Nat (slotLinkWords * 2)) :=
  match o with
  | .tcb t => some (t.spaceCells, t.spaceLinks)
  | _ => none

/-- The untyped record an object is, none for any other object.  The part of
the store the capability invariant's untyped facts read: an untyped's region,
which bounds its capabilities' free indices, and the children it records. -/
def untyped? (o : KernelObject) : Option UntypedObject :=
  match o with
  | .untyped u => some u
  | _ => none

/-- The notification-binding codes an object holds: a thread's bound-notification
code and a notification's bound-thread code, each `id + 1` or `0`; every other
kind holds neither.  The part of the store the notification binding reciprocity
reads. -/
@[inline] def bindingCodes (o : KernelObject) : Nat × Nat :=
  match o with
  | .tcb t => (t.boundNotificationCode, 0)
  | .notification n => (0, n.boundTCBCode)
  | _ => (0, 0)

/-- **The table back-links an object holds**: an endpoint's service record
while a service is registered on it (the flag and the registration's words,
`Endpoint.service`; the clear record otherwise, so a clear flag is a clear
back-link whatever words an endpoint carries) and a notification's interrupt
flag; every other kind holds neither.  The part of the
store the table references read: a registration names an endpoint, an interrupt
names a notification, and each of those objects records the entry that names it
(`SystemState.tableReferencesRecorded`).

WS-ZA ZA5.11: and **the taint words** a thread or a notification holds (the
carved words, the empty taint, on every other kind): the declassification
taint table names objects by id outside every slot too, and each object records
the entry naming it, so a write keeping an object's back-links keeps its taint
(`kindPreservingWrite`, `SystemState.TableReferenceFrame`).  Only threads and
notifications hold content (`contentTrackedFields`), so only they hold taint. -/
@[inline] def tableBackLinks (o : KernelObject) :
    EndpointService × Bool × SeLe4n.Kernel.TaintWords :=
  match o with
  | .endpoint ep => (if ep.serviceRegistered then ep.service else {}, false, {})
  | .notification n => ({}, n.irqBound, n.taintWords)
  | .tcb t => ({}, false, t.taintWords)
  | _ => ({}, false, {})

/-- WS-ZA ZA5.11: **the taint words an object holds** — a thread's or a
notification's; the carved words on every other kind. -/
@[inline] def taintWords (o : KernelObject) : SeLe4n.Kernel.TaintWords :=
  o.tableBackLinks.2.2

/-- WS-ZA ZA5.11: **the object with its taint words written** — a thread or a
notification; every other kind holds none and is returned as it is. -/
@[inline] def withTaintWords (o : KernelObject) (w : SeLe4n.Kernel.TaintWords) : KernelObject :=
  match o with
  | .tcb t => .tcb (t.withTaintWords w)
  | .notification n => .notification (n.withTaintWords w)
  | o => o

/-- WS-ZA ZA5.11: **the object with its taint words carved clean** — the
erasure the relation "equal modulo taint" is stated through
(`SystemState.objectsAgreeOffTaint`). -/
@[inline] def eraseTaint (o : KernelObject) : KernelObject := o.withTaintWords {}

/-- WS-ZA ZA5.11: **the object holds taint words** — a thread or a
notification, the two kinds that hold content (`contentTrackedFields`). -/
@[inline] def holdsTaint (o : KernelObject) : Bool :=
  match o with
  | .tcb _ => true
  | .notification _ => true
  | _ => false

/-- Writing an object's words leaves its kind. -/
@[simp] theorem holdsTaint_withTaintWords (o : KernelObject) (w : SeLe4n.Kernel.TaintWords) :
    (o.withTaintWords w).holdsTaint = o.holdsTaint := by
  cases o <;> rfl

/-- An object that holds no words reads the carved ones. -/
theorem taintWords_of_not_holdsTaint {o : KernelObject} (h : o.holdsTaint = false) :
    o.taintWords = {} := by
  cases o <;> first | rfl | (simp [holdsTaint] at h)

/-- A holder reads back the words written into it. -/
theorem taintWords_withTaintWords {o : KernelObject} (h : o.holdsTaint = true)
    (w : SeLe4n.Kernel.TaintWords) : (o.withTaintWords w).taintWords = w := by
  cases o <;> first | rfl | (simp [holdsTaint] at h)

/-- A word write changes no back-link but the words. -/
theorem tableBackLinks_withTaintWords {o : KernelObject} (h : o.holdsTaint = true)
    (w : SeLe4n.Kernel.TaintWords) :
    (o.withTaintWords w).tableBackLinks = (o.tableBackLinks.1, o.tableBackLinks.2.1, w) := by
  cases o <;> first | rfl | (simp [holdsTaint] at h)

/-- A word write keeps the interrupt back-link, on every kind. -/
@[simp] theorem tableBackLinks_withTaintWords_irq (o : KernelObject)
    (w : SeLe4n.Kernel.TaintWords) :
    (o.withTaintWords w).tableBackLinks.2.1 = o.tableBackLinks.2.1 := by
  cases o <;> rfl

/-- Erasure forgets every word write. -/
@[simp] theorem eraseTaint_withTaintWords (o : KernelObject) (w : SeLe4n.Kernel.TaintWords) :
    (o.withTaintWords w).eraseTaint = o.eraseTaint := by
  cases o <;> rfl

/-- A second word write overrides the first. -/
@[simp] theorem withTaintWords_withTaintWords (o : KernelObject) (w w' : SeLe4n.Kernel.TaintWords) :
    (o.withTaintWords w).withTaintWords w' = o.withTaintWords w' := by
  cases o <;> rfl

/-- A word write keeps the kind. -/
@[simp] theorem objectType_withTaintWords (o : KernelObject) (w : SeLe4n.Kernel.TaintWords) :
    (o.withTaintWords w).objectType = o.objectType := by
  cases o <;> rfl

/-- A word write keeps every capability slot. -/
@[simp] theorem slotCap_withTaintWords (o : KernelObject) (w : SeLe4n.Kernel.TaintWords) :
    (o.withTaintWords w).slotCap = o.slotCap := by
  cases o <;> rfl

/-- A word write keeps a thread's slots and their links. -/
@[simp] theorem tcbSlots_withTaintWords (o : KernelObject) (w : SeLe4n.Kernel.TaintWords) :
    (o.withTaintWords w).tcbSlots = o.tcbSlots := by
  cases o <;> rfl

/-- A holder is no CNode. -/
theorem objectType_ne_cnode_of_holdsTaint {o : KernelObject} (h : o.holdsTaint = true) :
    o.objectType ≠ KernelObjectType.cnode := by
  cases o <;> simp_all [holdsTaint, objectType]

/-- A word write keeps the binding codes. -/
@[simp] theorem bindingCodes_withTaintWords (o : KernelObject) (w : SeLe4n.Kernel.TaintWords) :
    (o.withTaintWords w).bindingCodes = o.bindingCodes := by
  cases o <;> rfl

/-- A kind holding no words is its own erasure. -/
theorem eraseTaint_of_not_holdsTaint {o : KernelObject} (h : o.holdsTaint = false) :
    o.eraseTaint = o := by
  cases o <;> first | rfl | (simp [holdsTaint] at h)

/-- **Erasure inverts off the holders**: an object agreeing off its words with
one of a kind holding none is that object. -/
theorem eq_of_eraseTaint_eq {o o' : KernelObject} (h' : o'.holdsTaint = false)
    (h : o'.eraseTaint = o.eraseTaint) : o = o' := by
  rw [eraseTaint_of_not_holdsTaint h'] at h
  have hH : o.holdsTaint = false := by
    rw [← holdsTaint_withTaintWords o {}]; exact (congrArg holdsTaint h).symm.trans h'
  rw [eraseTaint_of_not_holdsTaint hH] at h
  exact h.symm

/-- **Erasure keeps a thread a thread.** -/
theorem eraseTaint_eq_tcb {o : KernelObject} {t' : TCB}
    (h : (KernelObject.tcb t').eraseTaint = o.eraseTaint) :
    ∃ t, o = .tcb t ∧ t'.withTaintWords {} = t.withTaintWords {} := by
  cases o <;> simp only [eraseTaint, withTaintWords, KernelObject.tcb.injEq, reduceCtorEq] at h
  exact ⟨_, rfl, h⟩

/-- **Erasure keeps a notification a notification.** -/
theorem eraseTaint_eq_notification {o : KernelObject} {n' : Notification}
    (h : (KernelObject.notification n').eraseTaint = o.eraseTaint) :
    ∃ n, o = .notification n ∧ n'.withTaintWords {} = n.withTaintWords {} := by
  cases o <;> simp only [eraseTaint, withTaintWords, KernelObject.notification.injEq,
    reduceCtorEq] at h
  exact ⟨_, rfl, h⟩

/-- **The mapping facts an object holds**: a VSpace root's ASID, translations
and mapping epochs, and a frame's base; every other kind holds none.  The part
of the store the mapping records read besides the slots: a root maps an address
to a physical page under an epoch, and a frame owns the page at its base
(`SystemState.liveMappingsRecorded`).  A frame's own epoch counter is not read:
the map advances it and no record names it. -/
@[inline] def mappingView (o : KernelObject) :
    Option (SeLe4n.ASID × SeLe4n.Kernel.RobinHood.RHTable SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions) ×
      SeLe4n.Kernel.RobinHood.RHTable SeLe4n.VAddr Nat) × Option SeLe4n.PAddr :=
  match o with
  | .vspaceRoot r => (some (r.asid, r.mappings, r.mappingEpochs), none)
  | .frame f => (none, some f.base)
  | _ => (none, none)

/-- Clearing an object's derivation links keeps its table back-links. -/
@[simp] theorem tableBackLinks_withoutLinks (o : KernelObject) :
    o.withoutLinks.tableBackLinks = o.tableBackLinks := by
  cases o <;> rfl

/-- A word write keeps the mapping facts. -/
@[simp] theorem mappingView_withTaintWords (o : KernelObject) (w : SeLe4n.Kernel.TaintWords) :
    (o.withTaintWords w).mappingView = o.mappingView := by
  cases o <;> rfl

/-- Clearing an object's derivation links keeps its mapping facts. -/
@[simp] theorem mappingView_withoutLinks (o : KernelObject) :
    o.withoutLinks.mappingView = o.mappingView := by
  cases o <;> rfl

/-- Clearing an object's derivation links keeps its binding codes. -/
@[simp] theorem bindingCodes_withoutLinks (o : KernelObject) :
    o.withoutLinks.bindingCodes = o.bindingCodes := by
  cases o <;> rfl

/-- Clearing an object's derivation links keeps its untyped record. -/
@[simp] theorem untyped?_withoutLinks (o : KernelObject) : o.withoutLinks.untyped? = o.untyped? := by
  cases o <;> rfl

theorem hasSlot_holdsSlots {o : KernelObject} {s : SeLe4n.Slot} (h : o.hasSlot s) :
    o.holdsSlots = true := by
  cases o <;> first | rfl | exact absurd h id

theorem slotCap_of_not_holdsSlots {o : KernelObject} (h : o.holdsSlots = false) (s : SeLe4n.Slot) :
    o.slotCap s = none := by
  cases o <;> first | rfl | simp [holdsSlots] at h

theorem setLinkWords_of_not_holdsSlots {o : KernelObject} (h : o.holdsSlots = false)
    (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) : o.setLinkWords s f c w = o := by
  cases o <;> first | rfl | simp [holdsSlots] at h

theorem linkAt_of_not_holdsSlots {o : KernelObject} (h : o.holdsSlots = false)
    (s : SeLe4n.Slot) (f : LinkField) : o.linkAt s f = none := by
  cases o <;> first | rfl | simp [holdsSlots] at h

@[simp] theorem slotCap_setLinkWords (o : KernelObject) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat)
    (s' : SeLe4n.Slot) : (o.setLinkWords s f c w).slotCap s' = o.slotCap s' := by
  cases o <;> rfl

@[simp] theorem hasSlot_setLinkWords (o : KernelObject) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat)
    (s' : SeLe4n.Slot) : (o.setLinkWords s f c w).hasSlot s' ↔ o.hasSlot s' := by
  cases o <;> exact Iff.rfl

@[simp] theorem holdsSlots_setLinkWords (o : KernelObject) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
    (o.setLinkWords s f c w).holdsSlots = o.holdsSlots := by
  cases o <;> rfl

@[simp] theorem withoutLinks_setLinkWords (o : KernelObject) (s : SeLe4n.Slot) (f : LinkField)
    (c w : Nat) : (o.setLinkWords s f c w).withoutLinks = o.withoutLinks := by
  cases o <;> rfl

@[simp] theorem objectType_setLinkWords (o : KernelObject) (s : SeLe4n.Slot) (f : LinkField)
    (c w : Nat) : (o.setLinkWords s f c w).objectType = o.objectType := by
  cases o <;> rfl

/-- A slot outside the object reads no link. -/
theorem linkAt_of_not_hasSlot {o : KernelObject} {s : SeLe4n.Slot} (h : ¬ o.hasSlot s)
    (f : LinkField) : o.linkAt s f = none := by
  cases o with
  | cnode cn =>
    show cn.linkAt s f = none
    have hb : cn.links.size ≤ CNode.linkBase s f := by
      unfold CNode.linkBase; rw [cn.links_size]
      have := Nat.mul_le_mul_left slotLinkWords (Nat.le_of_not_lt h); omega
    unfold CNode.linkAt CNode.linkNodeWord decodeLink
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hb]; rfl
  | tcb t => exact t.spaceLinkAt_of_ge (Nat.le_of_not_lt h) f
  | _ => rfl

/-- Writing link words at a slot outside the object changes no link. -/
theorem linkWords_setLinkWords_of_not_hasSlot {o : KernelObject} {s : SeLe4n.Slot}
    (h : ¬ o.hasSlot s) (f : LinkField) (c w : Nat) :
    (o.setLinkWords s f c w).linkWords = o.linkWords := by
  have hf : f.offset + 1 < slotLinkWords := by
    cases f <;> simp [LinkField.offset, slotLinkWords]
  cases o with
  | cnode cn =>
    have hb : cn.links.size ≤ CNode.linkBase s f := by
      unfold CNode.linkBase; rw [cn.links_size]
      have := Nat.mul_le_mul_left slotLinkWords (Nat.le_of_not_lt h); omega
    show ((cn.links.setIfInBounds _ c).setIfInBounds _ w) = cn.links
    rw [Array.setIfInBounds_eq_of_size_le hb,
      Array.setIfInBounds_eq_of_size_le (by omega : cn.links.size ≤ CNode.linkBase s f + 1)]
  | tcb t =>
    have hs : 2 ≤ s.toNat := Nat.le_of_not_lt h
    have hb : t.spaceLinks.toArray.size ≤ CNode.linkBase s f := by
      rw [Vector.size_toArray]; unfold CNode.linkBase slotLinkWords; omega
    show ((t.spaceLinks.setIfInBounds _ c).setIfInBounds _ w).toArray = t.spaceLinks.toArray
    simp only [Vector.toArray_setIfInBounds]
    rw [Array.setIfInBounds_eq_of_size_le hb,
      Array.setIfInBounds_eq_of_size_le (by omega : t.spaceLinks.toArray.size ≤ CNode.linkBase s f + 1)]
  | _ => rfl

theorem linkAt_eq_of_linkWords_eq {o o' : KernelObject} (h : o'.linkWords = o.linkWords) :
    o'.linkAt = o.linkAt := by
  funext s f; rw [linkAt_eq_linkWords, linkAt_eq_linkWords, h]

/-- **Two objects of one kind other than a CNode, holding the same thread
slots** (`tcbSlots`), read the same slots, links and slot set: both are threads
with the same space cells and link words, or both hold no slot. -/
theorem slots_eq_of_tcbSlots {o o' : KernelObject} (hT : o'.objectType = o.objectType)
    (hN : o'.objectType ≠ .cnode) (hS : o'.tcbSlots = o.tcbSlots) :
    o'.slotCap = o.slotCap ∧ o'.linkWords = o.linkWords ∧ o'.linkAt = o.linkAt ∧
      (∀ s, o'.hasSlot s ↔ o.hasSlot s) ∧ o'.holdsSlots = o.holdsSlots := by
  have hW : o'.linkWords = o.linkWords := by
    cases o' <;> cases o <;> simp_all [objectType, tcbSlots, linkWords]
  refine ⟨?_, hW, linkAt_eq_of_linkWords_eq hW, ?_, ?_⟩
  · funext s
    cases o' <;> cases o <;> simp_all [objectType, tcbSlots, slotCap, TCB.spaceSlotCap]
  · intro s
    cases o' <;> cases o <;> simp_all [objectType, tcbSlots, hasSlot]
  · cases o' <;> cases o <;> simp_all [objectType, holdsSlots]

/-- An object of no slot-holding kind has no thread slots. -/
@[simp] theorem tcbSlots_of_not_tcb {o : KernelObject} (h : ∀ t, o ≠ .tcb t) : o.tcbSlots = none := by
  cases o <;> first | rfl | exact absurd rfl (h _)

@[simp] theorem tcbSlots_tcb (t : TCB) : (KernelObject.tcb t).tcbSlots = some (t.spaceCells, t.spaceLinks) := rfl

/-- The capabilities the object's slots hold, with their slots: a CNode's
occupied slots, a thread's occupied space slots; none for any other object. -/
noncomputable def slotCaps (o : KernelObject) : List (SeLe4n.Slot × Capability) :=
  match o with
  | .cnode cn => cn.slots.toList
  | .tcb t => t.spaceSlotCaps
  | _ => []

/-- **The object's slot store is well formed**: a CNode's slot map is unique
(`CNode.slotsUnique`), and a thread's slot store has its two cells.  Both hold
by construction (`slotsUnique_holds`). -/
def slotsUnique (o : KernelObject) : Prop :=
  match o with
  | .cnode cn => cn.slotsUnique
  | .tcb t => t.spaceCells.toArray.size = 2
  | _ => True

theorem slotsUnique_holds (o : KernelObject) : o.slotsUnique := by
  cases o
  case cnode cn => exact CNode.slotsUnique_holds cn
  case tcb t => exact Vector.size_toArray _
  all_goals trivial

/-- An object neither a CNode nor a thread holds no slot and reads no link. -/
theorem slotCap_linkAt_of_not_slots {o : KernelObject} (hC : ∀ cn, o ≠ .cnode cn)
    (hS : o.tcbSlots = none) : o.slotCap = (fun _ => none) ∧ o.linkAt = (fun _ _ => none) := by
  cases o
  case cnode cn => exact absurd rfl (hC cn)
  case tcb t => cases hS
  all_goals exact ⟨rfl, rfl⟩

/-- **Two objects that are the same CNode or neither, and hold the same thread
slots, read the same slots and links**, whatever their kinds otherwise. -/
theorem slots_eq_of_cnode_iff {o o' : KernelObject} (hC : ∀ cn, o' = .cnode cn ↔ o = .cnode cn)
    (hS : o'.tcbSlots = o.tcbSlots) : o'.slotCap = o.slotCap ∧ o'.linkAt = o.linkAt := by
  by_cases hc : ∃ cn, o' = .cnode cn
  · obtain ⟨cn, rfl⟩ := hc
    rw [(hC cn).mp rfl]; exact ⟨rfl, rfl⟩
  · have hc' : ∀ cn, o' ≠ .cnode cn := fun cn h => hc ⟨cn, h⟩
    have hc0 : ∀ cn, o ≠ .cnode cn := fun cn h => hc' cn ((hC cn).mpr h)
    cases ht : o'.tcbSlots with
    | none =>
      rw [ht] at hS
      rw [(slotCap_linkAt_of_not_slots hc' ht).1, (slotCap_linkAt_of_not_slots hc' ht).2,
        (slotCap_linkAt_of_not_slots hc0 hS.symm).1, (slotCap_linkAt_of_not_slots hc0 hS.symm).2]
      exact ⟨rfl, rfl⟩
    | some p =>
      rw [ht] at hS
      cases o' <;> simp [tcbSlots] at ht
      rename_i t'
      cases o <;> simp [tcbSlots] at hS
      rename_i t
      rw [← ht] at hS
      simp only [Prod.mk.injEq] at hS
      obtain ⟨hc1, hl1⟩ := hS
      have hW : (KernelObject.tcb t').linkWords = (KernelObject.tcb t).linkWords := by
        simp only [linkWords, hl1]
      exact ⟨funext fun s => by simp only [slotCap, TCB.spaceSlotCap, hc1],
        linkAt_eq_of_linkWords_eq hW⟩

/-- `slots_eq_of_cnode_iff` over a store's optional entries: the same slot reads
and link reads, present or absent. -/
theorem optSlots_eq_of_cnode_iff {a a' : Option KernelObject}
    (hC : ∀ cn, a' = some (.cnode cn) ↔ a = some (.cnode cn))
    (hS : a'.bind tcbSlots = a.bind tcbSlots) :
    (∀ s, (a'.bind fun o => o.slotCap s) = a.bind fun o => o.slotCap s) ∧
      (∀ s f, (a'.bind fun o => o.linkAt s f) = a.bind fun o => o.linkAt s f) := by
  cases a' <;> cases a
  case none.none => exact ⟨fun _ => rfl, fun _ _ => rfl⟩
  case none.some o =>
    have h := slotCap_linkAt_of_not_slots (o := o)
      (fun cn e => by have := (hC cn).mpr (by rw [e]); cases this) hS.symm
    exact ⟨fun s => by show none = o.slotCap s; rw [h.1],
      fun s f => by show none = o.linkAt s f; rw [h.2]⟩
  case some.none o' =>
    have h := slotCap_linkAt_of_not_slots (o := o')
      (fun cn e => by have := (hC cn).mp (by rw [e]); cases this) hS
    exact ⟨fun s => by show o'.slotCap s = none; rw [h.1],
      fun s f => by show o'.linkAt s f = none; rw [h.2]⟩
  case some.some o' o =>
    have h := slots_eq_of_cnode_iff (o := o) (o' := o')
      (fun cn => by simpa using hC cn) hS
    exact ⟨fun s => by show o'.slotCap s = o.slotCap s; rw [h.1],
      fun s f => by show o'.linkAt s f = o.linkAt s f; rw [h.2]⟩

/-- **Emptying slot `s` of an object** empties that slot and leaves every other
slot's capability. -/
theorem slotCap_removeSlotCap (o : KernelObject) (s s' : SeLe4n.Slot) :
    (o.removeSlotCap s).slotCap s' = if s' = s then none else o.slotCap s' := by
  cases o with
  | cnode cn =>
    show (cn.remove s).lookup s' = if s' = s then none else cn.lookup s'
    by_cases he : s' = s
    · subst he
      rw [if_pos rfl]
      exact CNode.lookup_remove_eq_none cn s' (CNode.slotsUnique_holds cn)
    · rw [if_neg he]
      exact CNode.lookup_remove_ne cn s s' (Ne.symm he) (CNode.slotsUnique_holds cn)
  | tcb t => exact t.spaceSlotCap_removeSpaceCap s s'
  | _ => split <;> rfl

/-- An object with a slot emptied holds no capability it did not hold. -/
theorem slotCap_removeSlotCap_back {o : KernelObject} {s s' : SeLe4n.Slot} {cap : Capability}
    (h : (o.removeSlotCap s).slotCap s' = some cap) : o.slotCap s' = some cap := by
  rw [slotCap_removeSlotCap] at h
  split at h
  · cases h
  · exact h

@[simp] theorem slotCap_removeSlotCap_self (o : KernelObject) (s : SeLe4n.Slot) :
    (o.removeSlotCap s).slotCap s = none := by
  rw [slotCap_removeSlotCap, if_pos rfl]

theorem slotCap_removeSlotCap_ne (o : KernelObject) {s s' : SeLe4n.Slot} (h : s' ≠ s) :
    (o.removeSlotCap s).slotCap s' = o.slotCap s' := by
  rw [slotCap_removeSlotCap, if_neg h]

/-- Emptying a slot writes no link word. -/
@[simp] theorem linkWords_removeSlotCap (o : KernelObject) (s : SeLe4n.Slot) :
    (o.removeSlotCap s).linkWords = o.linkWords := by
  cases o <;> rfl

theorem linkAt_removeSlotCap (o : KernelObject) (s : SeLe4n.Slot) :
    (o.removeSlotCap s).linkAt = o.linkAt :=
  linkAt_eq_of_linkWords_eq (linkWords_removeSlotCap o s)

@[simp] theorem hasSlot_removeSlotCap (o : KernelObject) (s s' : SeLe4n.Slot) :
    (o.removeSlotCap s).hasSlot s' ↔ o.hasSlot s' := by
  cases o <;> exact Iff.rfl

@[simp] theorem holdsSlots_removeSlotCap (o : KernelObject) (s : SeLe4n.Slot) :
    (o.removeSlotCap s).holdsSlots = o.holdsSlots := by
  cases o <;> rfl

@[simp] theorem objectType_removeSlotCap (o : KernelObject) (s : SeLe4n.Slot) :
    (o.removeSlotCap s).objectType = o.objectType := by
  cases o <;> rfl

end KernelObject

end SeLe4n.Model
