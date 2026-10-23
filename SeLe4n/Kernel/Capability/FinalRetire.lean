-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.UntypedReset
import SeLe4n.Model.CapabilityFinality
import SeLe4n.Kernel.Architecture.PageTeardownClears

/-!
# Retiring a memory object with its final capability

WS-ZA ZA5.4 part 21 (plan D2).  seL4's `cteDelete` runs `finaliseCap` on a
capability when `isFinalCapability` holds, and the object goes with its last
capability.  For the four memory kinds a carve makes — a frame, a page table,
an address-space root and an untyped — the finalisation is the unmap and
detach the teardown already does (`finaliseDestroyedCapabilities`); this module
is what follows it: the object leaves the store (`retireCarvedObject`, the
store's one erase, which the untyped reset uses too).

**What is decided before the slot is emptied** (`slotRetireTarget`): the
capability names a memory object by `.object`, the capability is final
(`SystemState.capIsFinal`, read from the slot's four link words), and the
object is retirable (`retirableKind`): a frame, a page table, a root, or an
untyped that records no child.  Under the capability bundle a final capability
is the only slot naming its object (`capIsFinal_iff_capFinalSpec`), so once the
slot is emptied no slot names it.

**What the untyped's child list needs.**  seL4 records nothing in an untyped
but its capability's free index: a carved object is found through the mapping
database alone.  This model's untypeds keep a child list besides
(`UntypedObject.children`), which the capability bundle reads: every child it
records is in the store (`TreeShapeOver.childLive`) and an object is recorded
by one untyped at most (`childUnique`).  So retiring an object takes it out of
the one list that records it too (`SystemState.unrecordChild`).  The recorder
is found before the slot is emptied (`recorderWord`): the slot's ancestors are
read through their parent words, each ancestor's capability naming an untyped
whose list records the object being the answer — the carve made the object's
capability a child of the capability it was carved through, and an object's
capabilities lie below every capability to its recorder (`carvedBelow`) — and
when none does, the store's untypeds are searched (`recorderInStore`), which
is what an object no untyped records (a boot object) costs.  Removing an
object from a list that records it shrinks the "carved from" relation and
leaves every other record, so `childLive`, `childUnique` and `carvedBelow`
hold after the retire (`TreeShapeOver.retire`).

**An untyped is retired only while it records no child.**  Until every kernel
object kind is finalised and retired with its last capability (part 22), a
kernel object can outlive its capabilities, recorded by its untyped alone.
Retiring that untyped would drop the record, and its own parent's reset would
then hand the object's memory to a new carve; so an untyped with a live record
stays in the store, unnamed, until its parent's reset retires it with the rest
of the carved subtree, as before this part.

**An address-space root** leaves the ASID table with it (`retireCarvedObject`
erases its entry and records the ASID's invalidation), and its ASID gets one
acknowledged `.aside1` round (`retypeAsidRoundStep`), the reset's own: a PE
that still holds the root's table in `TTBR0_EL1` leaves it before the next
carve can hand that page out.

The erase needs headroom in the object table (`size < capacity`), which every
insert leaves; the retire reads it and does nothing on a full table, so it never
refuses.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  An untyped's child list, read and shrunk without a closure
-- ============================================================================

/-- **Whether a child list records `x`**: the list walked in place, so no
closure or `Option` is built. -/
def childListRecords : List UntypedChild → SeLe4n.ObjId → Bool
  | [], _ => false
  | ch :: rest, x => ch.objId == x || childListRecords rest x

/-- **A child list without its records of `x`**: `List.filter`, written as a
recursion so an exclusively owned list is rewritten in place. -/
def childListErase : List UntypedChild → SeLe4n.ObjId → List UntypedChild
  | [], _ => []
  | ch :: rest, x => if ch.objId == x then childListErase rest x else ch :: childListErase rest x

theorem childListRecords_iff (l : List UntypedChild) (x : SeLe4n.ObjId) :
    childListRecords l x = true ↔ ∃ ch ∈ l, ch.objId = x := by
  induction l with
  | nil => simp [childListRecords]
  | cons ch rest ih => simp [childListRecords, ih]

theorem mem_childListErase {l : List UntypedChild} {x : SeLe4n.ObjId} {ch : UntypedChild} :
    ch ∈ childListErase l x ↔ ch ∈ l ∧ ch.objId ≠ x := by
  induction l with
  | nil => simp [childListErase]
  | cons c rest ih =>
    unfold childListErase
    by_cases h : c.objId = x
    · simp only [h, beq_self_eq_true, ↓reduceIte, ih, List.mem_cons]
      constructor
      · rintro ⟨hm, hn⟩; exact ⟨Or.inr hm, hn⟩
      · rintro ⟨rfl | hm, hn⟩
        · exact absurd h hn
        · exact ⟨hm, hn⟩
    · have hb : (c.objId == x) = false := by simpa using h
      simp only [hb, Bool.false_eq_true, ↓reduceIte, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨hm, hn⟩)
        · exact ⟨Or.inl rfl, h⟩
        · exact ⟨Or.inr hm, hn⟩
      · rintro ⟨rfl | hm, hn⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hm, hn⟩

theorem childListErase_eq_filter (l : List UntypedChild) (x : SeLe4n.ObjId) :
    childListErase l x = l.filter (fun ch => ch.objId != x) := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    unfold childListErase
    by_cases h : c.objId = x
    · simp [h, ih]
    · have hb : (c.objId == x) = false := by simpa using h
      simp [hb, ih, h]

-- ============================================================================
-- §2  The untyped that records an object
-- ============================================================================

/-- **Whether the untyped at `w` records `x`** in its child list. -/
@[inline] def untypedRecordsChild (st : SystemState) (w x : SeLe4n.ObjId) : Bool :=
  match st.objects[w]? with
  | some (.untyped U) => childListRecords U.children x
  | _ => false

theorem untypedRecordsChild_iff (st : SystemState) (w x : SeLe4n.ObjId) :
    untypedRecordsChild st w x = true ↔ SystemState.recordsChild st.getUntyped? w x := by
  unfold untypedRecordsChild SystemState.recordsChild
  cases h : st.objects[w]? with
  | none => simp [SystemState.getUntyped?, h]
  | some o =>
    cases o <;> simp [SystemState.getUntyped?, h, childListRecords_iff]

/-- **The recorder among a slot's ancestors**, as a word (`w + 1` for the
untyped `w`, `0` for none): the slot's parent is read from its two parent link
words, and the first ancestor whose capability names an untyped recording `x`
gives the answer.  `fuel` bounds the climb; the kernel passes one more than the
tree's edge bound.  Word reads only. -/
def recorderAbove (st : SystemState) (x : SeLe4n.ObjId) :
    Nat → SeLe4n.ObjId → SeLe4n.Slot → Nat
  | 0, _, _ => 0
  | n + 1, cnode, slot =>
    let pc := st.slotLinkNodeWord cnode slot .parent
    if pc = 0 then 0
    else
      let pn := SeLe4n.ObjId.ofNat (pc - 1)
      let ps := SeLe4n.Slot.ofNat (st.slotLinkSlotWord cnode slot .parent - 1)
      match st.slotCapAt ⟨pn, ps⟩ with
      | some k =>
        match k.target with
        | .object w =>
          if untypedRecordsChild st w x then w.val + 1 else recorderAbove st x n pn ps
        | _ => recorderAbove st x n pn ps
      | none => recorderAbove st x n pn ps

/-- **The recorder of `x` searched for in the store**, as a word: the first
untyped the object table holds whose child list records `x`. -/
def recorderInStore (st : SystemState) (x : SeLe4n.ObjId) : Nat :=
  st.objects.fold 0 fun acc k o =>
    if acc != 0 then acc
    else
      match o with
      | .untyped U => if childListRecords U.children x then k.val + 1 else 0
      | _ => 0

/-- **The untyped recording `x`**, read before the capability in slot `slot` of
`cnode` is destroyed, as a word: the slot's ancestors first
(`recorderAbove`), then the store (`recorderInStore`). -/
@[inline] def recorderWord (st : SystemState) (x : SeLe4n.ObjId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) : Nat :=
  let w := recorderAbove st x (st.cdt.edgeBound + 1) cnode slot
  if w != 0 then w else recorderInStore st x

theorem recorderAbove_spec (st : SystemState) (x : SeLe4n.ObjId) :
    ∀ (n : Nat) (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot),
      recorderAbove st x n cnode slot = 0 ∨
        ∃ w, recorderAbove st x n cnode slot = w.val + 1 ∧ untypedRecordsChild st w x = true
  | 0, _, _ => .inl rfl
  | n + 1, cnode, slot => by
    unfold recorderAbove
    dsimp only
    split
    · exact .inl rfl
    · split
      · split
        · split
          · next w _ hR => exact .inr ⟨w, rfl, hR⟩
          · exact recorderAbove_spec st x n _ _
        · exact recorderAbove_spec st x n _ _
      · exact recorderAbove_spec st x n _ _

/-- The store search's body: an answer found is kept, otherwise an untyped
recording `x` gives its word. -/
private theorem recorderInStore_step {x : SeLe4n.ObjId} {acc : Nat} {k : SeLe4n.ObjId}
    {o : KernelObject} :
    (if acc != 0 then acc
      else match o with
        | .untyped U => if childListRecords U.children x then k.val + 1 else 0
        | _ => 0) = 0 → acc = 0 ∧ ∀ U, o = .untyped U → childListRecords U.children x = false := by
  intro h
  by_cases ha : acc = 0
  · subst ha
    refine ⟨rfl, fun U hU => ?_⟩
    subst hU
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    cases hr : childListRecords U.children x
    · rfl
    · rw [hr] at h; simp at h
  · simp [ha] at h

/-- **What the store search answers**: a word it gives names an untyped
recording `x`, and when it gives none, no untyped records `x`. -/
theorem recorderInStore_spec (st : SystemState) (x : SeLe4n.ObjId) (hInv : st.objects.invExt) :
    (recorderInStore st x = 0 ∨
      ∃ w, recorderInStore st x = w.val + 1 ∧ untypedRecordsChild st w x = true) ∧
    (recorderInStore st x = 0 → ∀ w, untypedRecordsChild st w x = false) := by
  refine ⟨?_, ?_⟩
  · unfold recorderInStore
    refine SeLe4n.Kernel.RobinHood.RHTable.fold_preserves_of_lookup st.objects 0 _
      (fun acc => acc = 0 ∨ ∃ w, acc = w.val + 1 ∧ untypedRecordsChild st w x)
      hInv (.inl rfl) (fun acc k o hGet hAcc => ?_)
    by_cases ha : acc = 0
    · subst ha
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      cases o with
      | untyped U =>
        dsimp only
        split
        · next hr =>
          refine .inr ⟨k, rfl, ?_⟩
          unfold untypedRecordsChild
          rw [show st.objects[k]? = some (.untyped U) from hGet]
          exact hr
        · exact .inl rfl
      | _ => exact .inl rfl
    · simp only [show (acc != 0) = true by simpa using ha, ↓reduceIte]
      exact hAcc
  · intro h0 w
    cases hw : st.objects[w]? with
    | none => simp [untypedRecordsChild, hw]
    | some v =>
      have hQ := SeLe4n.Kernel.RobinHood.RHTable.fold_pointwise st.objects 0
        (fun acc k o =>
          if acc != 0 then acc
          else match o with
            | .untyped U => if childListRecords U.children x then k.val + 1 else 0
            | _ => 0)
        (fun _ _ => True)
        (fun k acc => acc = 0 → untypedRecordsChild st k x = false) hInv
        (fun _ => trivial) (fun _ _ _ _ _ _ => trivial)
        (fun acc k o hGet _ hz => by
          obtain ⟨-, hU⟩ := recorderInStore_step hz
          unfold untypedRecordsChild
          rw [show st.objects[k]? = some o from hGet]
          cases o with
          | untyped U => exact hU U rfl
          | _ => rfl)
        (fun acc k k' o' _ hQ hz => hQ (recorderInStore_step hz).1)
        w v hw
      exact hQ h0

/-- **What the recorder read answers**: a word it gives names an untyped
recording `x`, and when it gives none, no untyped records `x`. -/
theorem recorderWord_spec (st : SystemState) (x cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot)
    (hInv : st.objects.invExt) :
    (recorderWord st x cnode slot ≠ 0 →
      untypedRecordsChild st (SeLe4n.ObjId.ofNat (recorderWord st x cnode slot - 1)) x = true) ∧
    (recorderWord st x cnode slot = 0 → ∀ w, untypedRecordsChild st w x = false) := by
  unfold recorderWord
  dsimp only
  obtain ⟨hS1, hS0⟩ := recorderInStore_spec st x hInv
  by_cases hA : recorderAbove st x (st.cdt.edgeBound + 1) cnode slot = 0
  · simp only [hA, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun hne => ?_, hS0⟩
    rcases hS1 with h | ⟨w, hw, hr⟩
    · exact absurd h hne
    · rw [hw]; simpa [SeLe4n.ObjId.ofNat] using hr
  · simp only [show (recorderAbove st x (st.cdt.edgeBound + 1) cnode slot != 0) = true by
      simpa using hA, ↓reduceIte]
    refine ⟨fun _ => ?_, fun h => absurd h hA⟩
    rcases recorderAbove_spec st x (st.cdt.edgeBound + 1) cnode slot with h | ⟨w, hw, hr⟩
    · exact absurd h hA
    · rw [hw]; simpa [SeLe4n.ObjId.ofNat] using hr

-- ============================================================================
-- §3  What a final delete retires, and the retire
-- ============================================================================

/-- **Whether the object at `x` is one a final delete retires**: a frame, a
page table, an address-space root, or an untyped whose child list records
nothing (see the module docstring for why an untyped with a live record
stays). -/
@[inline] def retirableKind (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  match st.objects[x]? with
  | some (.frame _) => true
  | some (.pageTable _) => true
  | some (.vspaceRoot _) => true
  | some (.untyped U) => U.children.isEmpty
  | _ => false

/-- **The object the capability in slot `slot` of `cnode` takes with it**, as a
word (`x + 1`, or `0` for none), read before the slot is emptied: the
capability names `x` by `.object`, `x` is retirable, and the capability is
final (`SystemState.capIsFinal`). -/
@[inline] def slotRetireTarget (st : SystemState) (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) :
    Nat :=
  match st.slotCapAt ⟨cnode, slot⟩ with
  | some c =>
    match c.target with
    | .object x => if retirableKind st x && st.capIsFinal cnode slot then x.val + 1 else 0
    | _ => 0
  | none => 0

/-- **The recorder of what slot `slot` of `cnode` retires**, as a word, read
before the slot is emptied: `0` when it retires nothing. -/
@[inline] def slotRetireRecorder (st : SystemState) (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) :
    Nat :=
  let t := slotRetireTarget st cnode slot
  if t = 0 then 0 else recorderWord st (SeLe4n.ObjId.ofNat (t - 1)) cnode slot

/-- **`x` taken out of the child list of the untyped at `w`**, written in its
slot. -/
@[inline] def unrecordChild (st : SystemState) (w x : SeLe4n.ObjId) : SystemState :=
  st.storeUntypedWith w fun U => { U with children := childListErase U.children x }

/-- **Retire what a final delete destroyed** (`target`, `recorder`: the words
`slotRetireTarget` and `slotRetireRecorder` read before the slot was emptied):
the object leaves its recorder's child list, then the store
(`retireCarvedObject`), and a root's ASID gets its acknowledged round.  Nothing
when the target word is `0`, or when the object table has no headroom for the
erase. -/
def retireFinalObject (executingCore : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) : SystemState :=
  if target = 0 then st
  else if st.objects.size < st.objects.capacity then
    let x := SeLe4n.ObjId.ofNat (target - 1)
    let st1 := if recorder = 0 then st else unrecordChild st (SeLe4n.ObjId.ofNat (recorder - 1)) x
    match st1.objects[x]? with
    | some (.vspaceRoot root) => retypeAsidRoundStep executingCore root.asid (retireCarvedObject st1 x)
    | _ => retireCarvedObject st1 x
  else st

-- ============================================================================
-- §4  The retire keeps the tree's shape
-- ============================================================================

/-- **Retiring an object no slot names keeps the shape.**  The slots and the
tree are unchanged; every object but `x` stays in the store; every untyped the
new reading has was an untyped before, of the same region, and records a subset
of what it recorded, none of it `x`.  So "carved from" only shrinks, every
record still names a live object, and no capability reads differently. -/
theorem _root_.SeLe4n.Model.SystemState.TreeShapeOver.retire
    {cdt : CapDerivationTree} {cap : SlotRef → Option Capability}
    {present present' : SeLe4n.ObjId → Prop} {ut ut' : SeLe4n.ObjId → Option UntypedObject}
    {off : SlotRef → Prop} (h : SystemState.TreeShapeOver cdt cap present ut off)
    {x : SeLe4n.ObjId} (hx : ∀ r, ¬ SystemState.namesAt cap r x)
    (hP : ∀ o, present o → o ≠ x → present' o)
    (hUt : ∀ u U', ut' u = some U' → ∃ U, ut u = some U ∧ U'.regionSize = U.regionSize ∧
      ∀ ch ∈ U'.children, ch ∈ U.children ∧ ch.objId ≠ x) :
    SystemState.TreeShapeOver cdt cap present' ut' off := by
  have hSome : ∀ {u}, ut' u ≠ none → ut u ≠ none := fun {u} hu => by
    cases h' : ut' u with
    | none => exact absurd h' hu
    | some U' =>
      obtain ⟨U, hU, -⟩ := hUt u U' h'
      rw [hU]; exact Option.some_ne_none _
  have hCap : ∀ {r u}, SystemState.untypedCapAt cap ut' r u → SystemState.untypedCapAt cap ut r u :=
    fun ⟨c, hc, ht, hu⟩ => ⟨c, hc, ht, hSome hu⟩
  have hCapBack : ∀ {r u}, SystemState.untypedCapAt cap ut r u → ut' u ≠ none →
      SystemState.untypedCapAt cap ut' r u :=
    fun ⟨c, hc, ht, _⟩ hu => ⟨c, hc, ht, hu⟩
  have hRec : ∀ {u y}, SystemState.recordsChild ut' u y → SystemState.recordsChild ut u y := by
    rintro u y ⟨U', hU', ch, hch, hc⟩
    obtain ⟨U, hU, -, hS⟩ := hUt u U' hU'
    exact ⟨U, hU, ch, (hS ch hch).1, hc⟩
  have hCarved : ∀ {u y}, SystemState.CarvedFrom ut' u y → SystemState.CarvedFrom ut u y := by
    intro u y hc
    induction hc with
    | child hr => exact .child (hRec hr)
    | trans _ hr ih => exact .trans ih (hRec hr)
  refine ⟨h.inTree, h.ordered, fun r o hr => hP o (h.live r o hr) (fun e => hx r (e ▸ hr)),
    h.below, fun u p r hp hr => h.chainLinear u p r (hCap hp) (hCap hr),
    fun u p r hp hr hpr => ?_, fun p c u U' ho hc ht hu hf r hr hru => ?_,
    fun u y hy p r hp hr => h.carvedBelow u y (hCarved hy) p r (hCap hp) hr,
    fun u U' hu ch hch => ?_, fun u v U' V' hu hv ch hch ch' hch' he => ?_,
    fun r u hr hu => hCapBack (h.untypedNamed r u hr (hSome hu)) hu, h.sameObjectContiguous⟩
  · obtain ⟨c, hc, hcu, hcr⟩ := h.chainFirst u p r (hCap hp) (hCap hr) hpr
    obtain ⟨-, -, -, hpu⟩ := hp
    exact ⟨c, hc, hCapBack hcu hpu, hcr⟩
  · obtain ⟨U, hU, hSz, -⟩ := hUt u U' hu
    exact h.notFullLeaf p c u U ho hc ht hU (hSz ▸ hf) r hr (hCap hru)
  · obtain ⟨U, hU, -, hS⟩ := hUt u U' hu
    exact hP _ (h.childLive u U hU ch (hS ch hch).1) (hS ch hch).2
  · obtain ⟨U, hU, -, hS⟩ := hUt u U' hu
    obtain ⟨V, hV, -, hS'⟩ := hUt v V' hv
    exact h.childUnique u v U V hU hV ch (hS ch hch).1 ch' (hS' ch' hch').1 he

-- ============================================================================
-- §5  What the retire writes
-- ============================================================================

/-- The record a retire leaves of an untyped that recorded `x`. -/
@[inline] def untypedWithoutChild (U : UntypedObject) (x : SeLe4n.ObjId) : UntypedObject :=
  { U with children := childListErase U.children x }

/-- **The unrecord is a store of the untyped**, or nothing where no untyped
stands. -/
theorem unrecordChild_cases (st : SystemState) (w x : SeLe4n.ObjId) :
    ((∀ U, st.objects[w]? ≠ some (.untyped U)) ∧ unrecordChild st w x = st) ∨
    ∃ U, st.objects[w]? = some (.untyped U) ∧
      storeObject w (.untyped (untypedWithoutChild U x)) st = .ok ((), unrecordChild st w x) := by
  cases hW : st.objects[w]? with
  | none =>
    refine .inl ⟨fun _ h => (by cases h), ?_⟩
    unfold unrecordChild SystemState.storeUntypedWith; rw [hW]
  | some o =>
    cases o with
    | untyped U =>
      exact .inr ⟨U, rfl, SystemState.storeObject_untyped_eq_storeUntypedWith hW
        (fun U => { U with children := childListErase U.children x })⟩
    | _ =>
      refine .inl ⟨fun _ h => (by cases h), ?_⟩
      all_goals (unfold unrecordChild SystemState.storeUntypedWith; rw [hW])

/-- **The unrecord's frame**: the table keeps its invariant and headroom, the
scheduler, the machine and the tree are unchanged, and every key holds what it
held, but an untyped, which loses its records of `x`. -/
theorem unrecordChild_frame (st : SystemState) (w x : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hSz : st.objects.size < st.objects.capacity) :
    (unrecordChild st w x).objects.invExt ∧
    (unrecordChild st w x).objects.size < (unrecordChild st w x).objects.capacity ∧
    (unrecordChild st w x).scheduler = st.scheduler ∧
    (unrecordChild st w x).machine = st.machine ∧
    (unrecordChild st w x).cdt = st.cdt ∧
    ∀ oid : SeLe4n.ObjId, (unrecordChild st w x).objects[oid]? = st.objects[oid]? ∨
      ∃ U, st.objects[oid]? = some (KernelObject.untyped U) ∧
        (unrecordChild st w x).objects[oid]? = some (KernelObject.untyped (untypedWithoutChild U x)) := by
  rcases unrecordChild_cases st w x with ⟨-, hE⟩ | ⟨U, hW, hS⟩
  · rw [hE]; exact ⟨hInv, hSz, rfl, rfl, rfl, fun _ => .inl rfl⟩
  · have hObj : (unrecordChild st w x).objects =
        st.objects.insert w (.untyped (untypedWithoutChild U x)) := by
      have hE := hS
      unfold storeObject at hE
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hE
      rw [← hE]
    refine ⟨storeObject_preserves_objects_invExt _ _ _ _ hInv hS, ?_,
      storeObject_scheduler_eq _ _ _ _ hS, storeObject_machine_eq _ _ _ _ hS,
      storeObject_cdt_eq _ _ _ _ hS, fun oid => ?_⟩
    · rw [hObj]
      exact SeLe4n.Kernel.RobinHood.RHTable.insert_size_lt_capacity _ _ _ hInv hSz
        st.objects.hCapGe4
    · by_cases hK : oid = w
      · subst hK
        exact .inr ⟨U, hW, storeObject_objects_eq _ _ _ _ hInv hS⟩
      · exact .inl (storeObject_objects_ne _ _ _ _ _ hK hInv hS)

/-- The retire of `id` leaves every other key. -/
theorem retireCarvedObject_objects_ne (st : SystemState) (id oid : SeLe4n.ObjId) (hK : oid ≠ id)
    (hInv : st.objects.invExt) (hSz : st.objects.size < st.objects.capacity) :
    (retireCarvedObject st id).objects[oid]? = st.objects[oid]? := by
  unfold retireCarvedObject
  split
  · have hNe : ¬(id == oid) = true := by intro h; exact hK (eq_of_beq h).symm
    exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_ne st.objects id oid hNe hInv hSz
  · rfl

theorem retireCarvedObject_scheduler_machine_cdt (st : SystemState) (id : SeLe4n.ObjId) :
    (retireCarvedObject st id).scheduler = st.scheduler ∧
    (retireCarvedObject st id).machine = st.machine ∧
    (retireCarvedObject st id).cdt = st.cdt := by
  unfold retireCarvedObject; split <;> exact ⟨rfl, rfl, rfl⟩

theorem retypeAsidRoundStep_cdt (ec : Concurrency.CoreId) (a : SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundStep ec a s).cdt = s.cdt := rfl

/-- **A final-delete retire write** of `x`: every key holds what it held, but
`x`, a carved object now absent, and untypeds that lost their records of `x`. -/
def finalRetireWrite (st st' : SystemState) (x : SeLe4n.ObjId) : Prop :=
  ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
    (oid = x ∧ carvedAt st oid ∧ st'.objects[oid]? = none) ∨
    ∃ U, st.objects[oid]? = some (KernelObject.untyped U) ∧
      st'.objects[oid]? = some (KernelObject.untyped (untypedWithoutChild U x))

/-- **The retire's frame**: the table keeps its invariant; the scheduler, the
machine and the tree are unchanged; and the objects change by a final-delete
retire write of the target. -/
theorem retireFinalObject_frame (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) :
    (retireFinalObject ec target recorder st).objects.invExt ∧
    (retireFinalObject ec target recorder st).scheduler = st.scheduler ∧
    (retireFinalObject ec target recorder st).machine = st.machine ∧
    (retireFinalObject ec target recorder st).cdt = st.cdt ∧
    finalRetireWrite st (retireFinalObject ec target recorder st)
      (SeLe4n.ObjId.ofNat (target - 1)) := by
  unfold retireFinalObject
  split
  · exact ⟨hInv, rfl, rfl, rfl, fun _ => .inl rfl⟩
  split
  · next hSz =>
    dsimp only
    generalize hX : SeLe4n.ObjId.ofNat (target - 1) = x
    have h1 : ∀ st1 : SystemState, st1 = (if recorder = 0 then st
        else unrecordChild st (SeLe4n.ObjId.ofNat (recorder - 1)) x) →
        st1.objects.invExt ∧ st1.objects.size < st1.objects.capacity ∧
        st1.scheduler = st.scheduler ∧ st1.machine = st.machine ∧ st1.cdt = st.cdt ∧
        ∀ oid : SeLe4n.ObjId, st1.objects[oid]? = st.objects[oid]? ∨
          ∃ U, st.objects[oid]? = some (KernelObject.untyped U) ∧
            st1.objects[oid]? = some (KernelObject.untyped (untypedWithoutChild U x)) := by
      intro st1 h; subst h
      split
      · exact ⟨hInv, hSz, rfl, rfl, rfl, fun _ => .inl rfl⟩
      · exact unrecordChild_frame st _ x hInv hSz
    generalize hS1 : (if recorder = 0 then st
        else unrecordChild st (SeLe4n.ObjId.ofNat (recorder - 1)) x) = st1
    obtain ⟨i1, room1, s1, m1, c1, w1⟩ := h1 st1 hS1.symm
    obtain ⟨i2, -, -, -, -⟩ := retireCarvedObject_frame st1 x i1 room1
    obtain ⟨s2, m2, c2⟩ := retireCarvedObject_scheduler_machine_cdt st1 x
    have hW : finalRetireWrite st (retireCarvedObject st1 x) x := by
      intro oid
      by_cases hK : oid = x
      · subst hK
        rcases (retireCarvedObject_frame st1 oid i1 room1).2.2.2.1 oid with e | ⟨hc, hn⟩
        · rw [e]; rcases w1 oid with e1 | h; exact .inl e1; exact .inr (.inr h)
        · refine .inr (.inl ⟨rfl, ?_, hn⟩)
          rcases w1 oid with e1 | ⟨U, hU, -⟩
          · unfold carvedAt at hc ⊢; rw [← e1]; exact hc
          · exact .inr (.inl ⟨U, hU⟩)
      · rw [retireCarvedObject_objects_ne st1 x oid hK i1 room1]
        rcases w1 oid with e1 | h
        · exact .inl e1
        · exact .inr (.inr h)
    have hAll : ∀ s : SystemState, s.objects = (retireCarvedObject st1 x).objects →
        s.scheduler = (retireCarvedObject st1 x).scheduler →
        s.machine = (retireCarvedObject st1 x).machine →
        s.cdt = (retireCarvedObject st1 x).cdt →
        s.objects.invExt ∧ s.scheduler = st.scheduler ∧ s.machine = st.machine ∧
          s.cdt = st.cdt ∧ finalRetireWrite st s x := by
      intro s hO hSc hM hC
      refine ⟨hO ▸ i2, hSc.trans (s2.trans s1), hM.trans (m2.trans m1), hC.trans (c2.trans c1),
        fun oid => ?_⟩
      rw [hO]; exact hW oid
    split
    · exact hAll _ (retypeAsidRoundStep_objects _ _ _) (retypeAsidRoundStep_scheduler _ _ _)
        (retypeAsidRoundStep_machine _ _ _) (retypeAsidRoundStep_cdt _ _ _)
    · exact hAll _ rfl rfl rfl rfl
  · exact ⟨hInv, rfl, rfl, rfl, fun _ => .inl rfl⟩

/-- **The retire touches only what a reset touches**: every key holds what it
held, or a kind the reset touches on both sides (`resetTouched`). -/
theorem finalRetireWrite.touched {st st' : SystemState} {x : SeLe4n.ObjId}
    (h : finalRetireWrite st st' x) (oid : SeLe4n.ObjId) :
    st'.objects[oid]? = st.objects[oid]? ∨
      (resetTouched st.objects[oid]? ∧ resetTouched st'.objects[oid]?) := by
  rcases h oid with e | ⟨-, hc, hn⟩ | ⟨U, hU, hU'⟩
  · exact .inl e
  · refine .inr ⟨?_, by rw [hn]; trivial⟩
    rcases hc with ⟨f, hf⟩ | ⟨u, hu⟩ | ⟨r, hr⟩ | ⟨p, hp⟩
    · rw [hf]; trivial
    · rw [hu]; trivial
    · rw [hr]; trivial
    · rw [hp]; trivial
  · rw [hU, hU']; exact .inr ⟨trivial, trivial⟩

/-- **After the retire no untyped records its target**, when the recorder word
answers truly and at most one untyped recorded the target — or the retire
wrote nothing. -/
theorem retireFinalObject_unrecorded (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt)
    (hRec : target ≠ 0 →
      (recorder ≠ 0 → untypedRecordsChild st (SeLe4n.ObjId.ofNat (recorder - 1))
        (SeLe4n.ObjId.ofNat (target - 1)) = true) ∧
      (recorder = 0 → ∀ w, untypedRecordsChild st w (SeLe4n.ObjId.ofNat (target - 1)) = false))
    (hUniq : ∀ u v, untypedRecordsChild st u (SeLe4n.ObjId.ofNat (target - 1)) = true →
      untypedRecordsChild st v (SeLe4n.ObjId.ofNat (target - 1)) = true → u = v) :
    retireFinalObject ec target recorder st = st ∨
    ∀ (u : SeLe4n.ObjId) (U' : UntypedObject),
      (retireFinalObject ec target recorder st).objects[u]? = some (KernelObject.untyped U') →
      ∀ ch ∈ U'.children, ch.objId ≠ SeLe4n.ObjId.ofNat (target - 1) := by
  unfold retireFinalObject
  split
  · exact .inl rfl
  split
  · next hT hSz =>
    right
    obtain ⟨hR1, hR0⟩ := hRec hT
    dsimp only
    generalize SeLe4n.ObjId.ofNat (target - 1) = x at hR1 hR0 hUniq ⊢
    -- what the unrecord leaves: no untyped recording `x`
    have h1 : ∀ (u : SeLe4n.ObjId) (U' : UntypedObject),
        (if recorder = 0 then st else unrecordChild st (SeLe4n.ObjId.ofNat (recorder - 1)) x).objects[u]? =
          some (KernelObject.untyped U') → ∀ ch ∈ U'.children, ch.objId ≠ x := by
      intro u U' hu ch hch hc
      split at hu
      · next h0 =>
        have := hR0 h0 u
        unfold untypedRecordsChild at this
        rw [hu] at this
        exact absurd ((childListRecords_iff _ _).mpr ⟨ch, hch, hc⟩) (by simp [this])
      · next h0 =>
        have hw := hR1 h0
        rcases unrecordChild_cases st (SeLe4n.ObjId.ofNat (recorder - 1)) x with ⟨hN, -⟩ | ⟨U, hW, hS⟩
        · unfold untypedRecordsChild at hw
          cases hO : st.objects[SeLe4n.ObjId.ofNat (recorder - 1)]? with
          | none => rw [hO] at hw; cases hw
          | some o =>
            cases o with
            | untyped U => exact hN U hO
            | _ => rw [hO] at hw; cases hw
        · by_cases hK : u = SeLe4n.ObjId.ofNat (recorder - 1)
          · subst hK
            rw [storeObject_objects_eq _ _ _ _ hInv hS] at hu
            cases hu
            exact (mem_childListErase.mp hch).2 hc
          · rw [storeObject_objects_ne _ _ _ _ _ hK hInv hS] at hu
            have hr : untypedRecordsChild st u x = true := by
              unfold untypedRecordsChild; rw [hu]
              exact (childListRecords_iff _ _).mpr ⟨ch, hch, hc⟩
            exact hK (hUniq _ _ hr hw)
    generalize hS1 : (if recorder = 0 then st
        else unrecordChild st (SeLe4n.ObjId.ofNat (recorder - 1)) x) = st1 at h1
    have hI1 : st1.objects.invExt ∧ st1.objects.size < st1.objects.capacity := by
      subst hS1; split
      · exact ⟨hInv, hSz⟩
      · exact ⟨(unrecordChild_frame st _ x hInv hSz).1, (unrecordChild_frame st _ x hInv hSz).2.1⟩
    have hR : ∀ (u : SeLe4n.ObjId) (U' : UntypedObject),
        (retireCarvedObject st1 x).objects[u]? = some (KernelObject.untyped U') →
        ∀ ch ∈ U'.children, ch.objId ≠ x := by
      intro u U' hu
      by_cases hK : u = x
      · subst hK
        rcases (retireCarvedObject_frame st1 u hI1.1 hI1.2).2.2.2.1 u with e | ⟨-, hn⟩
        · rw [e] at hu; exact h1 u U' hu
        · rw [hn] at hu; cases hu
      · rw [retireCarvedObject_objects_ne st1 x u hK hI1.1 hI1.2] at hu
        exact h1 u U' hu
    split
    · intro u U' hu
      rw [retypeAsidRoundStep_objects] at hu
      exact hR u U' hu
    · exact hR
  · exact .inl rfl

-- ============================================================================
-- §6  The retire keeps the teardown's state well formed
-- ============================================================================

open SeLe4n.Kernel.RobinHood in
/-- **Retiring a carved object keeps the teardown's state well formed and only
shrinks roots**: every root after it was a root before it, and a retired root's
ASID leaves the table with it — the one entry naming it, as the table and the
roots agree and distinct roots carry distinct ASIDs. -/
theorem retireCarvedObject_preserves_teardownWellFormed (st : SystemState) (x : SeLe4n.ObjId)
    (hW : teardownWellFormed st) (hSz : st.objects.size < st.objects.capacity) :
    teardownWellFormed (retireCarvedObject st x) ∧ vspaceRootsShrink st (retireCarvedObject st x) := by
  obtain ⟨hI, hK, hB⟩ := hW
  obtain ⟨hI', -, -, -, hSelf⟩ := retireCarvedObject_frame st x hI hSz
  have hNe : ∀ o : SeLe4n.ObjId, o ≠ x → (retireCarvedObject st x).objects[o]? = st.objects[o]? :=
    fun o h => retireCarvedObject_objects_ne st x o h hI hSz
  have hBack : ∀ (o : SeLe4n.ObjId) (r : VSpaceRoot),
      (retireCarvedObject st x).objects[o]? = some (KernelObject.vspaceRoot r) →
      st.objects[o]? = some (KernelObject.vspaceRoot r) := by
    intro o r h
    by_cases hx : o = x
    · subst hx
      rcases (retireCarvedObject_frame st o hI hSz).2.2.2.1 o with e | ⟨-, hn⟩
      · rwa [← e]
      · rw [hn] at h; cases h
    · rwa [← hNe o hx]
  have hShrink : vspaceRootsShrink st (retireCarvedObject st x) :=
    fun oid r' h' => ⟨r', hBack oid r' h', rfl, fun _ _ hm => hm, fun _ _ he => he, fun _ hs => hs⟩
  refine ⟨?_, hShrink⟩
  cases hR : st.getVSpaceRoot? x with
  | none =>
    have hA : (retireCarvedObject st x).asidTable = st.asidTable := by
      unfold retireCarvedObject; split <;> simp [hR]
    refine teardownWellFormed_of_roots_eq hI' hA (fun o r => ⟨hBack o r, fun h => ?_⟩) ⟨hI, hK, hB⟩
    by_cases hx : o = x
    · subst hx
      rw [(SystemState.getVSpaceRoot?_eq_some_iff st o r).mpr h] at hR; cases hR
    · rwa [hNe o hx]
  | some r0 =>
    have hX : st.objects[x]? = some (KernelObject.vspaceRoot r0) :=
      (SystemState.getVSpaceRoot?_eq_some_iff st x r0).mp hR
    have hGuard : ((st.getFrame? x).isSome || (st.getUntyped? x).isSome ||
        (st.getVSpaceRoot? x).isSome || (st.getPageTable? x).isSome) = true := by
      simp [hR]
    have hA : (retireCarvedObject st x).asidTable = st.asidTable.erase r0.asid := by
      unfold retireCarvedObject; rw [if_pos hGuard]; simp [hR]
    have hXn : (retireCarvedObject st x).objects[x]? = none :=
      hSelf (.inr (.inr (.inr (.inl ⟨r0, hX⟩))))
    refine ⟨hI', hA ▸ RHTable.erase_preserves_invExtK _ _ hK, ?_⟩
    unfold Architecture.vspaceInvariantBundle Architecture.vspaceAsidRootsUnique
      Architecture.vspaceRootNonOverlap Architecture.asidTableConsistent
      Architecture.wxExclusiveInvariant Architecture.boundedAddressTranslation
      Architecture.vspaceCrossAsidIsolation Architecture.canonicalAddressInvariant
      Architecture.vspaceMappingsWellFormed at hB ⊢
    obtain ⟨c1, c2, ⟨c3a, c3b⟩, c4, c5, c6, c7, c8⟩ := hB
    refine ⟨fun o1 o2 r1 r2 h1 h2 => c1 o1 o2 r1 r2 (hBack _ _ h1) (hBack _ _ h2),
      fun o r h => c2 o r (hBack _ _ h), ⟨fun a o hT => ?_, fun o r h => ?_⟩,
      fun o r v p q h => c4 o r v p q (hBack _ _ h),
      fun o r v p q h => c5 o r v p q (hBack _ _ h),
      fun o1 o2 r1 r2 h1 h2 => c6 o1 o2 r1 r2 (hBack _ _ h1) (hBack _ _ h2),
      fun o r v p q h => c7 o r v p q (hBack _ _ h),
      fun o r h => c8 o r (hBack _ _ h)⟩
    · rw [hA] at hT
      by_cases ha : a = r0.asid
      · subst ha
        have := RHTable.getElem?_erase_self st.asidTable r0.asid hK.1
        rw [show (st.asidTable.erase r0.asid)[r0.asid]? = (st.asidTable.erase r0.asid).get? r0.asid
          from rfl, this] at hT
        cases hT
      · have hNeK : ¬(r0.asid == a) = true := by
          intro h; exact ha (eq_of_beq h).symm
        rw [show (st.asidTable.erase r0.asid)[a]? = (st.asidTable.erase r0.asid).get? a from rfl,
          RHTable.getElem?_erase_ne st.asidTable r0.asid a hNeK hK.1 hK.2.1] at hT
        obtain ⟨r, hr, hra⟩ := c3a a o hT
        have hox : o ≠ x := by
          intro e; subst e; rw [hX] at hr; cases hr; exact ha hra.symm
        exact ⟨r, by rw [hNe o hox]; exact hr, hra⟩
    · have hox : o ≠ x := by intro e; subst e; rw [hXn] at h; cases h
      have hr := hBack o r h
      have hAs : r.asid ≠ r0.asid := c6 o x r r0 hr hX hox
      have hNeK : ¬(r0.asid == r.asid) = true := by
        intro h; exact hAs (eq_of_beq h).symm
      rw [hA, show (st.asidTable.erase r0.asid)[r.asid]? = (st.asidTable.erase r0.asid).get? r.asid
        from rfl, RHTable.getElem?_erase_ne st.asidTable r0.asid r.asid hNeK hK.1 hK.2.1]
      exact c3b o r hr

theorem unrecordChild_asidTable (st : SystemState) (w x : SeLe4n.ObjId) :
    (unrecordChild st w x).asidTable = st.asidTable := by
  rcases unrecordChild_cases st w x with ⟨-, hE⟩ | ⟨U, hW, hS⟩
  · rw [hE]
  · rw [storeObject_asidTable_non_vspaceRoot _ _ _ _ (fun _ h => by cases h) hS, hW]

/-- **The retire keeps the teardown's state well formed and only shrinks
roots**: the unrecord writes an untyped where an untyped stands, the retire
takes one carved object out (`retireCarvedObject_preserves_teardownWellFormed`),
and the ASID round writes neither the objects nor the ASID table. -/
theorem retireFinalObject_preserves_teardownWellFormed (ec : Concurrency.CoreId)
    (target recorder : Nat) (st : SystemState) (hW : teardownWellFormed st) :
    teardownWellFormed (retireFinalObject ec target recorder st) ∧
      vspaceRootsShrink st (retireFinalObject ec target recorder st) := by
  unfold retireFinalObject
  split
  · exact ⟨hW, vspaceRootsShrink.refl st⟩
  split
  · next hSz =>
    dsimp only
    generalize SeLe4n.ObjId.ofNat (target - 1) = x
    have h1 : ∀ st1 : SystemState, st1 = (if recorder = 0 then st
        else unrecordChild st (SeLe4n.ObjId.ofNat (recorder - 1)) x) →
        teardownWellFormed st1 ∧ vspaceRootsShrink st st1 ∧
          st1.objects.size < st1.objects.capacity := by
      intro st1 h; subst h
      split
      · exact ⟨hW, vspaceRootsShrink.refl st, hSz⟩
      · obtain ⟨hI, hZ, -, -, -, hK⟩ := unrecordChild_frame st (SeLe4n.ObjId.ofNat (recorder - 1)) x hW.1 hSz
        have hR : ∀ (oid : SeLe4n.ObjId) (r : VSpaceRoot),
            (unrecordChild st (SeLe4n.ObjId.ofNat (recorder - 1)) x).objects[oid]? =
              some (KernelObject.vspaceRoot r) ↔ st.objects[oid]? = some (KernelObject.vspaceRoot r) := by
          intro oid r
          rcases hK oid with e | ⟨U, hU, hU'⟩
          · rw [e]
          · rw [hU, hU']; simp
        refine ⟨teardownWellFormed_of_roots_eq hI (unrecordChild_asidTable _ _ _) hR hW,
          fun oid r' h' => ⟨r', (hR oid r').1 h', rfl, fun _ _ hm => hm, fun _ _ he => he,
            fun _ hs => hs⟩, hZ⟩
    generalize hS1 : (if recorder = 0 then st
        else unrecordChild st (SeLe4n.ObjId.ofNat (recorder - 1)) x) = st1
    obtain ⟨hW1, hS1', hRoom1⟩ := h1 st1 hS1.symm
    obtain ⟨hW2, hS2⟩ := retireCarvedObject_preserves_teardownWellFormed st1 x hW1 hRoom1
    split
    · refine ⟨teardownWellFormed_of_tables_eq (retypeAsidRoundStep_objects _ _ _)
        (retypeAsidRoundStep_asidTable _ _ _) hW2, ?_⟩
      refine hS1'.trans (hS2.trans ?_)
      intro oid r' h'
      rw [retypeAsidRoundStep_objects] at h'
      exact ⟨r', h', rfl, fun _ _ hm => hm, fun _ _ he => he, fun _ hs => hs⟩
    · exact ⟨hW2, hS1'.trans hS2⟩
  · exact ⟨hW, vspaceRootsShrink.refl st⟩
