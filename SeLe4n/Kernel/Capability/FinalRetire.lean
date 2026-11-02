-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.CarvedObjectErase
import SeLe4n.Model.CapabilityFinality
import SeLe4n.Kernel.Architecture.PageTeardownClears

/-!
# Retiring an object with its final capability

WS-ZA ZA5.4 part 21 (plan D2).  seL4's `cteDelete` runs `finaliseCap` on a
capability when `isFinalCapability` holds, and the object goes with its last
capability.  For the four memory kinds a carve makes — a frame, a page table,
an address-space root and an untyped — the finalisation is the unmap and
detach the teardown already does (`finaliseDestroyedCapabilities`); this module
is what follows it: the object leaves the store (`retireCarvedObject`, the
store's one erase of a carved object).

**The passive kernel kinds** (part 22, `v0.36.133`).  An endpoint, a
notification, a reply or a CNode goes the same way when seL4's `finaliseCap`
would have nothing to cancel (`passiveObjectQuiescent`, read off the object's
own links) and nothing names it outside a slot (`passiveObjectRetirable`: no
service registration, no interrupt handler); it leaves the store
first (`eraseRetiredObject`), then its recorder's list.  No object names a
quiescent one by id under the reachable invariants
(`passiveObjectQuiescent.namedByNone`), so the guard walks no object table.  One
that fails either check outlives its last capability, recorded; its
finalisation (`finaliseFinalObject`) is what brings it here.

**What is decided before the slot is emptied** (`slotRetireTarget`): the
capability names the object (`Capability.namedObject`), the capability is final
(`SystemState.capIsFinal`, read from the slot's four link words), and the
object is retirable (`retirableKind`): a frame, a page table, a root, an
untyped, or a passive kernel kind.  Under the capability bundle a final capability
is the only slot naming its object (`capIsFinal_iff_capFinalSpec`), so once the
slot is emptied no slot names it.

**What the untyped's child list needs.**  seL4 records nothing in an untyped
but its capability's free index: a carved object is found through the mapping
database alone.  This model's untypeds keep a child list besides
(`UntypedObject.children`), which the capability bundle reads: every child it
records is in the store (`TreeShapeOver.childLive`) and an object is recorded
by one untyped at most (`childUnique`).  So retiring an object takes it out of
the one list that records it too (`retireUnrecord`).  The recorder
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

**An untyped that still records children** (part 26, `v0.36.139`) is retired
like any other, its children handed to its recorder as seL4's mapping database
splices a deleted node's children into its parent: the recorder records each
child in place of the untyped, its offset rebased onto the untyped's
(`childListAdopt`), and each child untyped names the recorder as its parent
(`reparentChildren`).  A child keeps its record, so the recorder's reset still
refuses while it lives (`untypedResetSlot`) and no carve is handed its memory; "carved from" only shrinks, since a
record moved up a level was carved from the recorder through the retired
untyped.  An untyped no untyped records (a boot untyped) leaves its children
recorded by none; its region is then covered by no untyped, so nothing carves
from it again.

**An address-space root** leaves the ASID table with it (`retireCarvedObject`
erases its entry and records the ASID's invalidation), and its ASID gets one
acknowledged `.aside1` round (`asidReleaseRound`): a PE
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

/-- **Child records moved one level up**: each offset rebased by `b`, the offset
of the untyped that recorded them within its own recorder. -/
def childListRebase : List UntypedChild → Nat → List UntypedChild
  | [], _ => []
  | c :: rest, b => { c with offset := b + c.offset } :: childListRebase rest b

/-- **seL4's derivation splice on a child list**: each record of `x` replaced by
`xs`, `x`'s own children (less any record of `x` itself), rebased onto that
record's offset.  With `xs` empty it is `childListErase` (`childListAdopt_nil`). -/
def childListAdopt : List UntypedChild → SeLe4n.ObjId → List UntypedChild → List UntypedChild
  | [], _, _ => []
  | ch :: rest, x, xs =>
    if ch.objId == x then childListRebase (childListErase xs x) ch.offset ++ childListAdopt rest x xs
    else ch :: childListAdopt rest x xs

theorem mem_childListRebase {l : List UntypedChild} {b : Nat} {c : UntypedChild} :
    c ∈ childListRebase l b → ∃ c0 ∈ l, c0.objId = c.objId := by
  induction l with
  | nil => simp [childListRebase]
  | cons a rest ih =>
    intro h
    simp only [childListRebase, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, List.mem_cons_self, rfl⟩
    · obtain ⟨c0, hm, he⟩ := ih h; exact ⟨c0, List.mem_cons_of_mem _ hm, he⟩

theorem childListRebase_nil (b : Nat) : childListRebase [] b = [] := rfl

theorem childListAdopt_nil (l : List UntypedChild) (x : SeLe4n.ObjId) :
    childListAdopt l x [] = childListErase l x := by
  induction l with
  | nil => rfl
  | cons ch rest ih =>
    unfold childListAdopt childListErase
    split <;> simp [ih, childListRebase]

theorem mem_childListAdopt {l xs : List UntypedChild} {x : SeLe4n.ObjId} {c : UntypedChild}
    (h : c ∈ childListAdopt l x xs) :
    c.objId ≠ x ∧ ((c ∈ l) ∨ (childListRecords l x = true ∧ ∃ c0 ∈ xs, c0.objId = c.objId)) := by
  induction l with
  | nil => simp [childListAdopt] at h
  | cons ch rest ih =>
    unfold childListAdopt at h
    by_cases hx : ch.objId = x
    · simp only [hx, beq_self_eq_true, ↓reduceIte, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨c0, hm, he⟩ := mem_childListRebase h
        have := mem_childListErase.mp hm
        refine ⟨he ▸ this.2, .inr ⟨?_, c0, this.1, he⟩⟩
        simp [childListRecords, hx]
      · obtain ⟨hn, h'⟩ := ih h
        refine ⟨hn, ?_⟩
        rcases h' with h' | ⟨_, h'⟩
        · exact .inl (List.mem_cons_of_mem _ h')
        · exact .inr ⟨by simp [childListRecords, hx], h'⟩
    · have hb : (ch.objId == x) = false := by simpa using hx
      simp only [hb, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨hx, .inl List.mem_cons_self⟩
      · obtain ⟨hn, h'⟩ := ih h
        refine ⟨hn, ?_⟩
        rcases h' with h' | ⟨hr, h'⟩
        · exact .inl (List.mem_cons_of_mem _ h')
        · exact .inr ⟨by simp [childListRecords, hr], h'⟩

theorem childListAdopt_of_not_records {l : List UntypedChild} {x : SeLe4n.ObjId}
    (kids : List UntypedChild) (h : childListRecords l x = false) : childListAdopt l x kids = l := by
  induction l with
  | nil => rfl
  | cons ch rest ih =>
    simp only [childListRecords, Bool.or_eq_false_iff] at h
    unfold childListAdopt
    rw [if_neg (by simpa using h.1), ih h.2]

-- ============================================================================
-- §2  The untyped that records an object
-- ============================================================================

/-- **Whether the untyped at `w` records `x`** in its child list. -/
@[inline] def untypedRecordsChild (st : SystemState) (w x : SeLe4n.ObjId) : Bool :=
  match st.getUntyped? w with
  | some U => childListRecords U.children x
  | none => false

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
          unfold untypedRecordsChild SystemState.getUntyped?
          rw [show st.objects[k]? = some (.untyped U) from hGet]
          exact hr
        · exact .inl rfl
      | _ => exact .inl rfl
    · simp only [show (acc != 0) = true by simpa using ha, ↓reduceIte]
      exact hAcc
  · intro h0 w
    cases hw : st.objects[w]? with
    | none => simp [untypedRecordsChild, SystemState.getUntyped?, hw]
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
          unfold untypedRecordsChild SystemState.getUntyped?
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
page table, an address-space root, an untyped (its children handed to its
recorder, `retireUnrecord`), or one of the four passive kernel kinds (an endpoint, a notification,
a reply or a CNode), which the retire takes out only while it is quiescent and
unreferenced (`passiveObjectRetirable`), or a thread or a scheduling context,
which the retire takes out only once the finalisation has left it detached
(`schedulingObjectRetirable`). -/
@[inline] def retirableKind (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  match st.getObjectType? x with
  | some .frame | some .pageTable | some .vspaceRoot => true
  | some .endpoint | some .notification | some .reply | some .cnode => true
  | some .tcb | some .schedContext => true
  | some .untyped => true
  | _ => false

/-- **The object the capability in slot `slot` of `cnode` takes with it**, as a
word (`x + 1`, or `0` for none), read before the slot is emptied: the
capability names `x` (`Capability.namedObject`: by `.object`, a reply
capability's reply, a CNode-slot capability's CNode), `x` is retirable, and
the capability is final (`SystemState.capIsFinal`). -/
@[inline] def slotRetireTarget (st : SystemState) (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) :
    Nat :=
  match st.slotCapAt ⟨cnode, slot⟩ with
  | some c =>
    match c.target with
    | .object x => if retirableKind st x && st.capIsFinal cnode slot then x.val + 1 else 0
    | .replyCap r =>
      if retirableKind st r.toObjId && st.capIsFinal cnode slot then r.toObjId.val + 1 else 0
    | .cnodeSlot cn _ => if retirableKind st cn && st.capIsFinal cnode slot then cn.val + 1 else 0
    | .auditTrail => 0
    | .schedControl _ => 0
  | none => 0

/-- The recorder word of the target word `t` (`0` for none), read from slot
`slot` of `cnode`. -/
@[inline] def recorderFor (st : SystemState) (t : Nat) (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) :
    Nat :=
  if t = 0 then 0 else recorderWord st (SeLe4n.ObjId.ofNat (t - 1)) cnode slot

/-- **The recorder of what slot `slot` of `cnode` retires**, as a word, read
before the slot is emptied: `0` when it retires nothing. -/
@[inline] def slotRetireRecorder (st : SystemState) (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) :
    Nat :=
  recorderFor st (slotRetireTarget st cnode slot) cnode slot

/-- **Whether destroying `cap`, held in slot `slot` of `cnode`, retires
nothing**: the check a delete's fast path asks of the capability it read
(`slotRetireTarget_eq_zero_iff`). -/
@[inline] def capabilityRetiresNothing (st : SystemState) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) (cap : Capability) : Bool :=
  match cap.target with
  | .object x => !(retirableKind st x && st.capIsFinal cnode slot)
  | .replyCap r => !(retirableKind st r.toObjId && st.capIsFinal cnode slot)
  | .cnodeSlot cn _ => !(retirableKind st cn && st.capIsFinal cnode slot)
  | .auditTrail => true
  | .schedControl _ => true

theorem slotRetireTarget_eq_zero_iff {st : SystemState} {cnode : SeLe4n.ObjId}
    {slot : SeLe4n.Slot} {cap : Capability} (h : st.slotCapAt ⟨cnode, slot⟩ = some cap) :
    slotRetireTarget st cnode slot = 0 ↔ capabilityRetiresNothing st cnode slot cap = true := by
  unfold slotRetireTarget capabilityRetiresNothing
  rw [h]
  dsimp only
  cases cap.target with
  | object x => cases retirableKind st x <;> cases st.capIsFinal cnode slot <;> simp
  | replyCap r => cases retirableKind st r.toObjId <;> cases st.capIsFinal cnode slot <;> simp
  | cnodeSlot cn _ => cases retirableKind st cn <;> cases st.capIsFinal cnode slot <;> simp
  | auditTrail => simp
  | schedControl _ => simp

theorem slotRetireTarget_of_empty {st : SystemState} {cnode : SeLe4n.ObjId}
    {slot : SeLe4n.Slot} (h : st.slotCapAt ⟨cnode, slot⟩ = none) :
    slotRetireTarget st cnode slot = 0 := by
  unfold slotRetireTarget; rw [h]

-- ============================================================================
-- §3a  The passive kernel kinds
-- ============================================================================

/-- **Whether an IPC state, held as its two codes, names the object `x`**: a
thread blocked on `x` as an endpoint (sending, receiving or calling) or as a
notification.  A caller awaiting its reply (state `4` and above) names no
object here: seL4's MCS caller is blocked on its reply object, which its reply
link names, and the endpoint word its state keeps records the call and is read
by no operation and no invariant, so the endpoint is freed when its last
capability goes (seL4's `finaliseCap`).  On the codes, so no state is built
(`ThreadIpcState.ofCodes`: state `0` is a send at object `o + 1`, the others
below `4` are on the object word itself). -/
@[inline] def ipcCodesName (objCode stateCode : Nat) (x : SeLe4n.ObjId) : Bool :=
  if stateCode = 0 then objCode == x.val + 1
  else if 4 ≤ stateCode then false
  else objCode == x.val

/-- **Whether an object names `x` by its id outside a slot**: a thread blocked
on it (`ipcCodesName`), bound to it as its notification, or linked to it as
its reply (a caller's reply, a receiver's stashed reply); another reply's
stack link to it; a scheduling context whose reply stack it heads.  These are
every reference by id an endpoint, a notification, a reply or a CNode can have
in an object; a capability naming it lies in a slot, which finality reads.
The retire reads none of these: each is answered by the object's own links
under the reachable invariants (`passiveObjectQuiescent.namedByNone`). -/
@[inline] def objectNamesById (o : KernelObject) (x : SeLe4n.ObjId) : Bool :=
  match o with
  | .tcb t =>
    ipcCodesName t.ipcObjectCode t.ipcStateCode x || t.boundNotificationCode == x.val + 1 ||
      t.replyObjectCode == x.val + 1 || t.pendingReceiveReplyCode == x.val + 1
  | .reply r =>
    (match r.prev with | some p => p.toObjId == x | none => false) ||
      (match r.next with | some (.frame a) => a.toObjId == x | _ => false)
  | .schedContext sc => match sc.scReply with | some r => r.toObjId == x | none => false
  | _ => false

/-- **Whether the object at `x` is a passive kernel kind**: an endpoint, a
notification, a reply or a CNode. -/
@[inline] def passiveKindAt (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  match st.getObjectType? x with
  | some .endpoint | some .notification | some .reply | some .cnode => true
  | _ => false

/-- **Whether the passive object at `x` is quiescent**, so seL4's `finaliseCap`
on its last capability has nothing to cancel: an endpoint whose two queues are
empty (`cancelAllIPC` wakes nobody); a notification with no waiter and no bound
thread (`unbindMaybeNotification` and `cancelAllSignals` do nothing); a reply
with no caller, stashed by no receiver and with no stack link (`reply_remove`
does nothing; seL4 clears a reply's `replyTCB` before it frees it, and a
stashed reply's stasher is read through the reply's own record,
`SystemState.replyStashedAt`, one field and one thread); a CNode whose every
slot is empty (the zombie loop deletes nothing), read as its occupancy links
heading nowhere (`CNode.occHead`), one word.  These own-link reads are the
whole test: under the reachable invariants no object names a quiescent
passive object (`passiveObjectQuiescent.namedByNone`). -/
@[inline] def passiveObjectQuiescent (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  match st.getObject? x with
  | some (.endpoint ep) => ep.sendHeadCode == 0 && ep.recvHeadCode == 0
  | some (.notification n) => n.waitHeadCode == 0 && n.boundTCBCode == 0
  | some (.reply r) =>
    r.callerCode == 0 && !st.replyStashedAt ⟨x.val⟩ r && r.prev.isNone && r.next.isNone
  | some (.cnode cn) => cn.occHead == 0
  | _ => false

/-- **Whether a final delete retires the passive object at `x`**: it is
quiescent, read off its own links, and it holds no table back-link
(`SystemState.tableBackLinksClear`) — no service registration records itself
on it and no interrupt names it, one field of the object read in place of a
walk of the registry and the interrupt table: the two answers agree on every
reachable state (`SystemState.tableReferencesRecorded`,
`SystemState.tableBackLinksClear.namedByNone`).  A passive object that fails
this outlives its last capability, as every kernel object did before
`v0.36.133`; the cancelling finalisation that brings one here is
`finaliseFinalObject`, after `releaseFinalRegistration` has dropped an
endpoint's service registration, so only an interrupt's notification still
fails the back-link half at its last capability. -/
@[inline] def passiveObjectRetirable (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  passiveObjectQuiescent st x && st.tableBackLinksClear x

-- ============================================================================
-- §3b  The thread and the scheduling context
-- ============================================================================

/-- **Whether the object at `x` is a thread or a scheduling context**, the two
kinds a final delete finalises before it retires them (part 24). -/
@[inline] def schedulingKindAt (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  match st.getObjectType? x with
  | some .tcb | some .schedContext => true
  | _ => false

/-- **Whether an object names the thread whose code is `c`** (`c = t.val + 1`,
`SeLe4n.ThreadId.optCode`) by id, on the codes, so nothing is built: a thread
linked to it in an endpoint queue, a notification queue, a run queue or a
reply-waiter queue, heading a reply-waiter queue at it, donated a context it
owns, or blocked on a reply it answers; an endpoint or a notification whose
queue starts or ends at it, a notification bound to it; a reply whose caller it
is; a scheduling context bound to it.  Each link is read as its readers read
it: a run-queue neighbour code only through a core code naming a core
(`TCB.runLinkOn`), a binding's owner code only through a context code
(`SchedContextBinding.ofCodes`).  The retire reads none of these: under the
reachable invariants and the binding pair no object names a retirable thread
(`threadRetirable.namedByNone`). -/
@[inline] def objectNamesThread (o : KernelObject) (c : Nat) : Bool :=
  match o with
  | .tcb t =>
    t.queueNextCode == c || t.queuePrevCode == c || t.queuePPrevCode == c + 1 ||
      t.ntfnNextCode == c || t.ntfnPrevCode == c ||
      (t.runCoreCode != 0 && t.runCoreCode ≤ Concurrency.numCores &&
        (t.runNextCode == c || t.runPrevCode == c || t.runBucketNextCode == c ||
          t.runBucketPrevCode == c)) ||
      t.replyWaiterNextCode == c || t.replyWaiterPrevCode == c ||
      t.replyWaitersHeadCode == c || (t.scBindingScCode != 0 && t.scBindingOwnerCode == c) ||
      t.ipcStateCode == c + 4
  | .endpoint ep =>
    ep.sendHeadCode == c || ep.sendTailCode == c || ep.recvHeadCode == c || ep.recvTailCode == c
  | .notification n => n.waitHeadCode == c || n.waitTailCode == c || n.boundTCBCode == c
  | .reply r => r.callerCode == c
  | .schedContext sc => sc.boundThreadCode == c
  | _ => false

/-- **Whether a thread's own record is quiescent but for its space slots**, so
seL4's `suspend` has nothing left to do and nothing it holds names another
object: `.Inactive` and `.ready`, with no pending message, no stashed or
awaited reply, no timeout budget; linked into no endpoint, notification, run or
reply-waiter queue and heading none; bound to no notification and to no
scheduling context; and (WS-ZA ZA6.6) yielded to no context, its yield link
cancelled as seL4's `suspend` cancels it.  What a thread's finalisation leaves, before the zombie
loop deletes its space slots.  Of the run-queue fields only the core code is
read: a thread whose core code is zero is on no core's queue, and its four
neighbour codes are then masked by every reader (`TCB.runLinkOn`,
`runMaxCodeWalk`, the compiled dequeue), so no invariant holds them at zero and
the guard does not read them; the retire erases the record with them. -/
@[inline] def threadLinksQuiescent (t : TCB) : Bool :=
  t.threadState == .Inactive && t.ipcStateCode == 0 && t.ipcObjectCode == 0 &&
    t.pendingMessage.isNone && t.queueNextCode == 0 && t.queuePrevCode == 0 &&
    t.queuePPrevCode == 0 && t.ntfnNextCode == 0 && t.ntfnPrevCode == 0 && t.runCoreCode == 0 &&
    t.replyWaiterNextCode == 0 && t.replyWaiterPrevCode == 0 &&
    t.replyWaitersHeadCode == 0 && t.scBindingScCode == 0 && t.scBindingOwnerCode == 0 &&
    t.boundNotificationCode == 0 && t.replyObjectCode == 0 && t.pendingReceiveReplyCode == 0 &&
    t.timeoutBudget.isNone && t.yieldToCode == 0

/-- **Whether a thread's own record is quiescent**: quiescent but for its space
slots (`threadLinksQuiescent`), and its two space slots empty. -/
@[inline] def threadQuiescent (t : TCB) : Bool :=
  threadLinksQuiescent t && t.spaceCells[0].isNone && t.spaceCells[1].isNone

/-- **Whether a final delete retires the thread at `x`**: the thread stored
under its own id, no core's idle thread, quiescent on its own links
(`threadQuiescent`) and held by no core (`threadHeldOnSomeCore`: current, FP
owner or resident nowhere).  A thread holds no table back-link, so no table
entry can name it.  The finalisation
(`finaliseSchedulingObject`) is what brings a thread here; one that fails
outlives its last capability. -/
@[inline] def threadRetirable (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  match st.getObject? x with
  | some (.tcb t) =>
    t.tid.val == x.val && !isIdleThreadId t.tid && threadQuiescent t &&
      !threadHeldOnSomeCore st t.tid
  | _ => false

/-- **Whether an object names the scheduling context whose code is `c`**
(`c = s.val + 1`) by id: a thread bound to it, lent it, or holding it as its
timeout budget; a reply whose stack it heads.  The retire guard does not ask it:
on the states the delete chain carries, no object names an admitted context
(`schedContextRetirable.tcbNamesNone`, `schedContextRetirable.namedByNone`). -/
@[inline] def objectNamesSchedContext (o : KernelObject) (c : Nat) : Bool :=
  match o with
  | .tcb t =>
    t.scBindingScCode == c || (match t.timeoutBudget with | some s => s.val + 1 == c | none => false)
  | .reply r => match r.next with | some (.head s) => s.val + 1 == c | _ => false
  | _ => false

/-- **Whether a final delete retires the scheduling context at `x`**, on the
context's own links — the links seL4's `finaliseCap` clears a scheduling
context through (`scTCB`, `scReply`): bound to no thread, lent from none and
heading no reply stack — and (WS-ZA ZA6.3) linked into no core's release queue,
so the erase never cuts a queue's chain; and (WS-ZA ZA6.6) recording no yielder,
its yield completed as seL4's context `finaliseCap` completes it, so the erase
never leaves a thread yielded to a context that is gone.  Nothing outside the context is walked.  What makes these the whole
truth is the scheduling links the delete chain carries
(`schedContextLinkInvariant`): a thread bound to a context, as its own or on
loan, is named by it back, no thread holds a timeout budget, and every context a
replenishment queue holds is bound — so no object names an admitted context
(`schedContextRetirable.namedByNone`) and no core queues it.  The finalisation
(`finaliseSchedulingObject`) is what brings a context here. -/
@[inline] def schedContextRetirable (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  match st.getObject? x with
  | some (.schedContext sc) =>
    sc.boundThreadCode == 0 && sc.donationOrigin.isNone && sc.scReply.isNone &&
      sc.releaseCoreCode == 0 && sc.yieldFromCode == 0
  | _ => false

/-- **Whether a final delete retires the thread or the scheduling context at
`x`.** -/
@[inline] def schedulingObjectRetirable (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  threadRetirable st x || schedContextRetirable st x

/-- **Whether a final delete retires its target `x` at all**: a memory object is
retired as part 21 retires it, a passive object only while
`passiveObjectRetirable` holds, and a thread or a scheduling context only while
`schedulingObjectRetirable` holds — never one its finalisation left in use,
whose untyped must keep recording it. -/
@[inline] def finalRetireAdmitted (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  (!passiveKindAt st x || passiveObjectRetirable st x) &&
    (!schedulingKindAt st x || schedulingObjectRetirable st x)

/-- **Whether the object at `x` is one the retire erases from the store**: a
passive kernel kind, a thread or a scheduling context.  A carved memory object
leaves through `retireCarvedObject` instead. -/
@[inline] def erasableKindAt (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  passiveKindAt st x || schedulingKindAt st x

/-- **Erase a retired kernel object** — an endpoint, a notification, a reply, a
CNode, a thread or a scheduling context (`erasableKindAt`) — from the object
store, with its index row, its index-set entry and its type, through the erase
primitives `retireCarvedObject` compiles to (`withObjectErased` and its index
and type companions, each out of line over the state it is handed, so the
tables are erased in place); the identity at any other key.  The record it
makes is `eraseRetiredObject_eq`.  `retireFinalObject` runs it only on an
object `finalRetireAdmitted` admits. -/
def eraseRetiredObject (st : SystemState) (x : SeLe4n.ObjId) : SystemState :=
  if erasableKindAt st x then
    withObjectTypeErased (withObjectIndexSetErased (withObjectUnindexed (withObjectErased st x) x) x) x
  else st

/-- **`eraseRetiredObject` as a record**: the object, its index row, its
index-set entry and its type erased, every other field kept. -/
theorem eraseRetiredObject_eq (st : SystemState) (x : SeLe4n.ObjId) :
    eraseRetiredObject st x =
      if erasableKindAt st x then
        { st with
            objects := st.objects.erase x
            objectIndex := st.objectIndex.filter (· != x)
            objectIndexSet := st.objectIndexSet.erase x
            lifecycle := { objectTypes := st.lifecycle.objectTypes.erase x } }
      else st := by
  unfold eraseRetiredObject withObjectTypeErased withObjectIndexSetErased
    withObjectUnindexed withObjectErased
  split
  · rw [objIdListDrop_eq_filter]; simp
  · rfl

/-- **The children the untyped at `x` records**, read before it is retired;
none when `x` holds no untyped. -/
@[inline] def retiredChildren (st : SystemState) (x : SeLe4n.ObjId) : List UntypedChild :=
  match st.getUntyped? x with
  | some X => X.children
  | none => []

/-- The parent an adopted child untyped names: the recorder word's untyped, or
none. -/
@[inline] def recorderParent (recorder : Nat) : Option SeLe4n.ObjId :=
  if recorder = 0 then none else some (SeLe4n.ObjId.ofNat (recorder - 1))

/-- **Each untyped a record of `kids` names takes the recorder as its parent**
(`recorderParent`), written in its slot; a record naming anything else is
skipped. -/
def reparentChildren (recorder : Nat) : List UntypedChild → SystemState → SystemState
  | [], st => st
  | c :: rest, st =>
    reparentChildren recorder rest
      (st.storeUntypedWith c.objId fun U => { U with parent := recorderParent recorder })

/-- **The untyped at `w` adopts `kids` in place of its records of `x`**
(`childListAdopt`), written in its slot. -/
@[inline] def adoptChildren (st : SystemState) (w x : SeLe4n.ObjId) (kids : List UntypedChild) :
    SystemState :=
  st.storeUntypedWith w fun U => { U with children := childListAdopt U.children x kids }

/-- **`x` taken out of the records**, seL4's derivation splice: each child
untyped `x` recorded names the recorder as its parent (`reparentChildren`), and
the recorder records `x`'s children in place of `x` (`adoptChildren`).  With no
recorder (a boot object) the children are recorded by none.  An object that is
no untyped records nothing, so this is then the erase of `x`'s record alone. -/
@[inline] def retireUnrecord (recorder : Nat) (x : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  let kids := retiredChildren st x
  let st0 := reparentChildren recorder kids st
  if recorder = 0 then st0 else adoptChildren st0 (SeLe4n.ObjId.ofNat (recorder - 1)) x kids

/-- A child `x` records, as the store reads it. -/
theorem mem_retiredChildren {st : SystemState} {x : SeLe4n.ObjId} {c : UntypedChild}
    (h : c ∈ retiredChildren st x) : untypedRecordsChild st x c.objId = true := by
  unfold retiredChildren at h
  unfold untypedRecordsChild
  cases hX : st.getUntyped? x with
  | none => rw [hX] at h; cases h
  | some X =>
    rw [hX] at h
    exact (childListRecords_iff _ _).mpr ⟨c, h, rfl⟩

/-- **The retire after the passive erase**: `x` leaves the child list of its
recorder (`recorder`, a word as `slotRetireRecorder` reads it), the recorder
adopting `x`'s own children (`retireUnrecord`), a carved `x`
leaves the store, and a root's ASID gets its acknowledged round.  `x`'s
declassification provenance leaves with it: a thread or a notification at `x`
is an erasable kind, so the passive erase takes its taint words out
(`retireFinalObject_taint_cleared`). -/
def retireRecordedObject (executingCore : Concurrency.CoreId) (recorder : Nat) (x : SeLe4n.ObjId)
    (st : SystemState) : SystemState :=
  let st1 := retireUnrecord recorder x st
  match st1.getVSpaceRoot? x with
  | some root => asidReleaseRound executingCore root.asid (retireCarvedObject st1 x)
  | none => retireCarvedObject st1 x

/-- **Retire what a final delete destroyed** (`target`, `recorder`: the words
`slotRetireTarget` and `slotRetireRecorder` read before the slot was emptied):
a passive kernel kind leaves the store (`eraseRetiredObject`, the identity on
any other kind), the object leaves its recorder's child list, a carved object
leaves the store (`retireCarvedObject`, the identity on an absent key), and a
root's ASID gets its acknowledged round.  Nothing when the target word is
`0`, when the object table has no headroom for the erase, or when the target is
a passive object `passiveObjectRetirable` refuses, which outlives its last
capability (`finalRetireAdmitted`). -/
def retireFinalObject (executingCore : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) : SystemState :=
  if target = 0 then st
  else if st.objects.size < st.objects.capacity then
    let x := SeLe4n.ObjId.ofNat (target - 1)
    if finalRetireAdmitted st x then
      retireRecordedObject executingCore recorder x (eraseRetiredObject st x)
    else st
  else st

-- ============================================================================
-- §4  The retire keeps the tree's shape
-- ============================================================================

/-- **Retiring an object no slot names keeps the shape.**  The slots and the
tree are unchanged; every object but `x` stays in the store, and `x` is no
untyped after; every untyped the new reading has was an untyped before, of the
same region, and each record it holds names what one of its records named, or
— the splice — a child of `x`, which it recorded.  None names `x`.  So "carved
from" only shrinks (a record moved up a level was carved from it through `x`),
every record still names a live object, an object is still recorded once (its
record moved off `x`, which is gone), and no capability reads differently. -/
theorem _root_.SeLe4n.Model.SystemState.TreeShapeOver.retire
    {cdt : CapDerivationTree} {cap : SlotRef → Option Capability}
    {present present' : SeLe4n.ObjId → Prop} {ut ut' : SeLe4n.ObjId → Option UntypedObject}
    {off : SlotRef → Prop} (h : SystemState.TreeShapeOver cdt cap present ut off)
    {x : SeLe4n.ObjId} (hx : ∀ r, ¬ SystemState.namesAt cap r x)
    (hP : ∀ o, present o → o ≠ x → present' o)
    (hUt : ∀ u U', ut' u = some U' → ∃ U, ut u = some U ∧ U'.regionSize = U.regionSize ∧
      ∀ ch ∈ U'.children, ch.objId ≠ x ∧
        ((∃ c ∈ U.children, c.objId = ch.objId) ∨
          (SystemState.recordsChild ut u x ∧ SystemState.recordsChild ut x ch.objId)))
    (hGone : ut' x = none) :
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
  -- a post record of `y` in `u` is a pre record, or `u` recorded `x`, which recorded `y`
  have hRec : ∀ {u y}, SystemState.recordsChild ut' u y →
      SystemState.recordsChild ut u y ∨
        (SystemState.recordsChild ut u x ∧ SystemState.recordsChild ut x y) := by
    rintro u y ⟨U', hU', ch, hch, hc⟩
    obtain ⟨U, hU, -, hS⟩ := hUt u U' hU'
    rcases (hS ch hch).2 with ⟨c, hcm, he⟩ | hr
    · exact .inl ⟨U, hU, c, hcm, he.trans hc⟩
    · exact .inr (hc ▸ hr)
  have hCarved : ∀ {u y}, SystemState.CarvedFrom ut' u y → SystemState.CarvedFrom ut u y := by
    have one : ∀ {u y}, SystemState.recordsChild ut' u y → SystemState.CarvedFrom ut u y :=
      fun hr => (hRec hr).elim .child fun ⟨a, b⟩ => .trans (.child a) b
    intro u y hc
    induction hc with
    | child hr => exact one hr
    | trans _ hr ih =>
      rcases hRec hr with hr' | ⟨a, b⟩
      · exact .trans ih hr'
      · exact .trans (.trans ih a) b
  have hUniq : ∀ {u v y}, SystemState.recordsChild ut u y → SystemState.recordsChild ut v y → u = v :=
    fun ⟨U, hU, ch, hch, hc⟩ ⟨V, hV, ch', hch', hc'⟩ =>
      h.childUnique _ _ U V hU hV ch hch ch' hch' (hc.trans hc'.symm)
  have hNotX : ∀ {v}, ut' v ≠ none → v ≠ x := fun {v} hv e => hv (e ▸ hGone)
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
    obtain ⟨hne, hm⟩ := hS ch hch
    refine hP _ ?_ hne
    rcases hm with ⟨c, hcm, he⟩ | ⟨-, X, hX, c, hcm, he⟩
    · exact he ▸ h.childLive u U hU c hcm
    · exact he ▸ h.childLive x X hX c hcm
  · have hu' : SystemState.recordsChild ut' u ch.objId := ⟨U', hu, ch, hch, rfl⟩
    have hv' : SystemState.recordsChild ut' v ch.objId := ⟨V', hv, ch', hch', he.symm⟩
    have hun : ut' u ≠ none := by rw [hu]; exact Option.some_ne_none _
    have hvn : ut' v ≠ none := by rw [hv]; exact Option.some_ne_none _
    rcases hRec hu' with a | ⟨a1, a2⟩ <;> rcases hRec hv' with b | ⟨b1, b2⟩
    · exact hUniq a b
    · exact absurd (hUniq a b2) (hNotX hun)
    · exact absurd (hUniq b a2) (hNotX hvn)
    · exact hUniq a1 b1

-- ============================================================================
-- §5  What the retire writes
-- ============================================================================

/-- **A store through `storeUntypedWith` is a store of the untyped**, or
nothing where no untyped stands: the table keeps its invariant and headroom,
the scheduler, the machine and the tree are unchanged, and only `w` changes. -/
theorem storeUntypedWith_frame (st : SystemState) (w : SeLe4n.ObjId)
    (f : UntypedObject → UntypedObject)
    (hInv : st.objects.invExt) (hSz : st.objects.size < st.objects.capacity) :
    (st.storeUntypedWith w f).objects.invExt ∧
    (st.storeUntypedWith w f).objects.size < (st.storeUntypedWith w f).objects.capacity ∧
    (st.storeUntypedWith w f).scheduler = st.scheduler ∧
    (st.storeUntypedWith w f).machine = st.machine ∧
    (st.storeUntypedWith w f).cdt = st.cdt ∧
    ∀ oid : SeLe4n.ObjId, (st.storeUntypedWith w f).objects[oid]? = st.objects[oid]? ∨
      ∃ U, oid = w ∧ st.objects[oid]? = some (KernelObject.untyped U) ∧
        (st.storeUntypedWith w f).objects[oid]? = some (KernelObject.untyped (f U)) := by
  cases hW : st.objects[w]? with
  | none =>
    have hE : st.storeUntypedWith w f = st := by unfold SystemState.storeUntypedWith; rw [hW]
    rw [hE]; exact ⟨hInv, hSz, rfl, rfl, rfl, fun _ => .inl rfl⟩
  | some o =>
    cases o with
    | untyped U =>
      have hS := SystemState.storeObject_untyped_eq_storeUntypedWith hW f
      have hObj : (st.storeUntypedWith w f).objects = st.objects.insert w (.untyped (f U)) := by
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
          exact .inr ⟨U, rfl, hW, storeObject_objects_eq _ _ _ _ hInv hS⟩
        · exact .inl (storeObject_objects_ne _ _ _ _ _ hK hInv hS)
    | _ =>
      all_goals
        have hE : st.storeUntypedWith w f = st := by unfold SystemState.storeUntypedWith; rw [hW]
        rw [hE]; exact ⟨hInv, hSz, rfl, rfl, rfl, fun _ => .inl rfl⟩

/-- **The reparent's frame**: only the untypeds the records name change, and
only in their parent. -/
theorem reparentChildren_frame (recorder : Nat) (kids : List UntypedChild) (st : SystemState)
    (hInv : st.objects.invExt) (hSz : st.objects.size < st.objects.capacity) :
    (reparentChildren recorder kids st).objects.invExt ∧
    (reparentChildren recorder kids st).objects.size <
      (reparentChildren recorder kids st).objects.capacity ∧
    (reparentChildren recorder kids st).scheduler = st.scheduler ∧
    (reparentChildren recorder kids st).machine = st.machine ∧
    (reparentChildren recorder kids st).cdt = st.cdt ∧
    ∀ oid : SeLe4n.ObjId, (reparentChildren recorder kids st).objects[oid]? = st.objects[oid]? ∨
      ∃ U U', st.objects[oid]? = some (KernelObject.untyped U) ∧
        (reparentChildren recorder kids st).objects[oid]? = some (KernelObject.untyped U') ∧
        U'.regionBase = U.regionBase ∧ U'.regionSize = U.regionSize ∧
        U'.isDevice = U.isDevice ∧ U'.children = U.children ∧ ∃ c ∈ kids, c.objId = oid := by
  induction kids generalizing st with
  | nil => exact ⟨hInv, hSz, rfl, rfl, rfl, fun _ => .inl rfl⟩
  | cons c rest ih =>
    obtain ⟨i1, hSz1, s1, m1, c1, w1⟩ := storeUntypedWith_frame st c.objId
      (fun U => { U with parent := recorderParent recorder }) hInv hSz
    obtain ⟨i2, hSz2, s2, m2, c2, w2⟩ := ih _ i1 hSz1
    refine ⟨i2, hSz2, s2.trans s1, m2.trans m1, c2.trans c1, fun oid => ?_⟩
    simp only [reparentChildren]
    rcases w2 oid with e2 | ⟨U1, U2, h1, h2, b, s, d, ch, k, hk, hko⟩ <;>
      rcases w1 oid with e1 | ⟨U, hK, hU, hU1⟩
    · exact .inl (e2.trans e1)
    · exact .inr ⟨U, _, hU, e2.trans hU1, rfl, rfl, rfl, rfl, c, List.mem_cons_self, hK.symm⟩
    · exact .inr ⟨U1, U2, e1 ▸ h1, h2, b, s, d, ch, k, List.mem_cons_of_mem _ hk, hko⟩
    · rw [hU1] at h1; cases h1
      exact .inr ⟨U, U2, hU, h2, b, s, d, ch, k, List.mem_cons_of_mem _ hk, hko⟩

theorem storeUntypedWith_asidTable (st : SystemState) (w : SeLe4n.ObjId)
    (f : UntypedObject → UntypedObject) : (st.storeUntypedWith w f).asidTable = st.asidTable := by
  cases hW : st.objects[w]? with
  | none => unfold SystemState.storeUntypedWith; rw [hW]
  | some o =>
    cases o with
    | untyped U =>
      rw [storeObject_asidTable_non_vspaceRoot _ _ _ _ (fun _ h => by cases h)
        (SystemState.storeObject_untyped_eq_storeUntypedWith hW f), hW]
    | _ => all_goals (unfold SystemState.storeUntypedWith; rw [hW])

theorem reparentChildren_asidTable (recorder : Nat) (kids : List UntypedChild) (st : SystemState) :
    (reparentChildren recorder kids st).asidTable = st.asidTable := by
  induction kids generalizing st with
  | nil => rfl
  | cons c rest ih => simp only [reparentChildren]; rw [ih, storeUntypedWith_asidTable]

theorem retireUnrecord_asidTable (recorder : Nat) (x : SeLe4n.ObjId) (st : SystemState) :
    (retireUnrecord recorder x st).asidTable = st.asidTable := by
  unfold retireUnrecord adoptChildren
  dsimp only
  split
  · exact reparentChildren_asidTable _ _ _
  · rw [storeUntypedWith_asidTable, reparentChildren_asidTable]

theorem storeUntypedWith_fields (st : SystemState) (w : SeLe4n.ObjId)
    (f : UntypedObject → UntypedObject) :
    (st.storeUntypedWith w f).cdt = st.cdt ∧ (st.storeUntypedWith w f).scheduler = st.scheduler ∧
      (st.storeUntypedWith w f).machine = st.machine := by
  cases hW : st.objects[w]? with
  | none => unfold SystemState.storeUntypedWith; rw [hW]; exact ⟨rfl, rfl, rfl⟩
  | some o =>
    cases o with
    | untyped U =>
      have hS := SystemState.storeObject_untyped_eq_storeUntypedWith hW f
      exact ⟨storeObject_cdt_eq _ _ _ _ hS, storeObject_scheduler_eq _ _ _ _ hS,
        storeObject_machine_eq _ _ _ _ hS⟩
    | _ => all_goals (unfold SystemState.storeUntypedWith; rw [hW]; exact ⟨rfl, rfl, rfl⟩)

theorem retireUnrecord_fields (recorder : Nat) (x : SeLe4n.ObjId) (st : SystemState) :
    (retireUnrecord recorder x st).cdt = st.cdt ∧
      (retireUnrecord recorder x st).scheduler = st.scheduler ∧
      (retireUnrecord recorder x st).machine = st.machine := by
  have hR : ∀ kids st, (reparentChildren recorder kids st).cdt = st.cdt ∧
      (reparentChildren recorder kids st).scheduler = st.scheduler ∧
      (reparentChildren recorder kids st).machine = st.machine := by
    intro kids
    induction kids with
    | nil => intro st; exact ⟨rfl, rfl, rfl⟩
    | cons c rest ih =>
      intro st
      simp only [reparentChildren]
      obtain ⟨a, b, d⟩ := ih (st.storeUntypedWith c.objId _)
      obtain ⟨a', b', d'⟩ := storeUntypedWith_fields st c.objId
        (fun U => { U with parent := recorderParent recorder })
      exact ⟨a.trans a', b.trans b', d.trans d'⟩
  unfold retireUnrecord adoptChildren
  dsimp only
  obtain ⟨a, b, d⟩ := hR (retiredChildren st x) st
  split
  · exact ⟨a, b, d⟩
  · obtain ⟨a', b', d'⟩ := storeUntypedWith_fields (reparentChildren recorder (retiredChildren st x) st)
      (SeLe4n.ObjId.ofNat (recorder - 1)) _
    exact ⟨a'.trans a, b'.trans b, d'.trans d⟩

theorem storeUntypedWith_tables (st : SystemState) (w : SeLe4n.ObjId)
    (f : UntypedObject → UntypedObject) (p : SeLe4n.ObjId → Bool) (hw : p w = false) :
    (st.storeUntypedWith w f).irqHandlers = st.irqHandlers ∧
      (st.storeUntypedWith w f).objectIndex.filter p = st.objectIndex.filter p := by
  cases hW : st.objects[w]? with
  | none => unfold SystemState.storeUntypedWith; rw [hW]; exact ⟨rfl, rfl⟩
  | some o =>
    cases o with
    | untyped U =>
      have hS := SystemState.storeObject_untyped_eq_storeUntypedWith hW f
      unfold storeObject at hS
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
      rw [← hS]
      refine ⟨rfl, ?_⟩
      dsimp only
      split
      · rfl
      · rw [List.filter_cons, hw]; rfl
    | _ => all_goals (unfold SystemState.storeUntypedWith; rw [hW]; exact ⟨rfl, rfl⟩)

/-- **The unrecord keeps the interrupt table, and the object index
on the keys a predicate admits**, when the predicate admits neither the
recorder nor a child `x` records. -/
theorem retireUnrecord_tables (recorder : Nat) (x : SeLe4n.ObjId) (st : SystemState)
    (p : SeLe4n.ObjId → Bool)
    (hR : recorder ≠ 0 → p (SeLe4n.ObjId.ofNat (recorder - 1)) = false)
    (hK : ∀ c ∈ retiredChildren st x, p c.objId = false) :
    (retireUnrecord recorder x st).irqHandlers = st.irqHandlers ∧
      (retireUnrecord recorder x st).objectIndex.filter p = st.objectIndex.filter p := by
  have hP : ∀ kids st, (∀ c ∈ kids, p c.objId = false) →
      (reparentChildren recorder kids st).irqHandlers = st.irqHandlers ∧
      (reparentChildren recorder kids st).objectIndex.filter p = st.objectIndex.filter p := by
    intro kids
    induction kids with
    | nil => intro st _; exact ⟨rfl, rfl⟩
    | cons c rest ih =>
      intro st hk
      simp only [reparentChildren]
      obtain ⟨b, d⟩ := ih (st.storeUntypedWith c.objId _) (fun c' hc' => hk c' (List.mem_cons_of_mem _ hc'))
      obtain ⟨b', d'⟩ := storeUntypedWith_tables st c.objId
        (fun U => { U with parent := recorderParent recorder }) p (hk c List.mem_cons_self)
      exact ⟨b.trans b', d.trans d'⟩
  unfold retireUnrecord adoptChildren
  dsimp only
  obtain ⟨b, d⟩ := hP (retiredChildren st x) st hK
  split
  · exact ⟨b, d⟩
  · next h0 =>
    obtain ⟨b', d'⟩ := storeUntypedWith_tables (reparentChildren recorder (retiredChildren st x) st)
      (SeLe4n.ObjId.ofNat (recorder - 1)) _ p (hR h0)
    exact ⟨b'.trans b, d'.trans d⟩

/-- **The unrecord's frame**: the table keeps its invariant and headroom, the
scheduler, the machine and the tree are unchanged, and every key holds what it
held, or an untyped of the same region whose child list is its own or its own
with `x`'s children adopted in place of `x`; a key that changes records `x` or
is one of `x`'s children. -/
theorem retireUnrecord_frame (recorder : Nat) (x : SeLe4n.ObjId) (st : SystemState)
    (hInv : st.objects.invExt) (hSz : st.objects.size < st.objects.capacity) :
    (retireUnrecord recorder x st).objects.invExt ∧
    (retireUnrecord recorder x st).objects.size < (retireUnrecord recorder x st).objects.capacity ∧
    (retireUnrecord recorder x st).scheduler = st.scheduler ∧
    (retireUnrecord recorder x st).machine = st.machine ∧
    (retireUnrecord recorder x st).cdt = st.cdt ∧
    ∀ oid : SeLe4n.ObjId, (retireUnrecord recorder x st).objects[oid]? = st.objects[oid]? ∨
      ∃ U U', st.objects[oid]? = some (KernelObject.untyped U) ∧
        (retireUnrecord recorder x st).objects[oid]? = some (KernelObject.untyped U') ∧
        U'.regionBase = U.regionBase ∧ U'.regionSize = U.regionSize ∧ U'.isDevice = U.isDevice ∧
        (U'.children = U.children ∨
          U'.children = childListAdopt U.children x (retiredChildren st x)) ∧
        (U' = U ∨ childListRecords U.children x = true ∨
          ∃ c ∈ retiredChildren st x, c.objId = oid) := by
  obtain ⟨i0, hSz0, s0, m0, c0, w0⟩ := reparentChildren_frame recorder (retiredChildren st x) st hInv hSz
  unfold retireUnrecord
  dsimp only
  generalize reparentChildren recorder (retiredChildren st x) st = st0 at i0 hSz0 s0 m0 c0 w0
  split
  · refine ⟨i0, hSz0, s0, m0, c0, fun oid => ?_⟩
    rcases w0 oid with e | ⟨U, U', hU, hU', b, s, d, ch, k⟩
    · exact .inl e
    · exact .inr ⟨U, U', hU, hU', b, s, d, .inl ch, .inr (.inr k)⟩
  · obtain ⟨i1, hSz1, s1, m1, c1, w1⟩ := storeUntypedWith_frame st0 (SeLe4n.ObjId.ofNat (recorder - 1))
      (fun U => { U with children := childListAdopt U.children x (retiredChildren st x) }) i0 hSz0
    refine ⟨i1, hSz1, s1.trans s0, m1.trans m0, c1.trans c0, fun oid => ?_⟩
    unfold adoptChildren
    rcases w1 oid with e1 | ⟨U1, -, hU1, hU2⟩ <;> rcases w0 oid with e0 | ⟨U, U', hU, hU', b, s, d, ch, k⟩
    · exact .inl (e1.trans e0)
    · exact .inr ⟨U, U', hU, e1.trans hU', b, s, d, .inl ch, .inr (.inr k)⟩
    · rw [e0] at hU1
      refine .inr ⟨U1, _, hU1, hU2, rfl, rfl, rfl, .inr rfl, ?_⟩
      cases hr : childListRecords U1.children x with
      | true => exact .inr (.inl rfl)
      | false =>
        refine .inl ?_
        rw [childListAdopt_of_not_records _ hr]
    · rw [hU'] at hU1; cases hU1
      exact .inr ⟨U, _, hU, hU2, b, s, d, .inr (by rw [ch]), .inr (.inr k)⟩

/-- **The recorder adopts**: with a nonzero recorder word naming an untyped,
the unrecord leaves that untyped recording `x`'s children in place of `x`. -/
theorem retireUnrecord_recorder (recorder : Nat) (x : SeLe4n.ObjId) (st : SystemState)
    (hInv : st.objects.invExt) (hSz : st.objects.size < st.objects.capacity) (h0 : recorder ≠ 0)
    {U : UntypedObject}
    (hU : st.objects[SeLe4n.ObjId.ofNat (recorder - 1)]? = some (KernelObject.untyped U)) :
    ∃ U', (retireUnrecord recorder x st).objects[SeLe4n.ObjId.ofNat (recorder - 1)]? =
        some (KernelObject.untyped U') ∧
      U'.children = childListAdopt U.children x (retiredChildren st x) := by
  obtain ⟨i0, hSz0, -, -, -, w0⟩ := reparentChildren_frame recorder (retiredChildren st x) st hInv hSz
  unfold retireUnrecord adoptChildren
  dsimp only
  rw [if_neg h0]
  generalize reparentChildren recorder (retiredChildren st x) st = st0 at i0 hSz0 w0
  have h1 : ∃ U1, st0.objects[SeLe4n.ObjId.ofNat (recorder - 1)]? = some (KernelObject.untyped U1) ∧
      U1.children = U.children := by
    rcases w0 (SeLe4n.ObjId.ofNat (recorder - 1)) with e | ⟨U0, U1, hU0, hU1, -, -, -, ch, -⟩
    · exact ⟨U, e.trans hU, rfl⟩
    · rw [hU] at hU0; cases hU0; exact ⟨U1, hU1, ch⟩
  obtain ⟨U1, hU1, hch⟩ := h1
  refine ⟨_, storeObject_objects_eq _ _ _ _ i0
    (SystemState.storeObject_untyped_eq_storeUntypedWith hU1 _), by simp only [hch]⟩

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

theorem asidReleaseRound_cdt (ec : Concurrency.CoreId) (a : SeLe4n.ASID) (s : SystemState) :
    (asidReleaseRound ec a s).cdt = s.cdt := rfl

/-- **The passive kernel kinds**, read off a key: an endpoint, a notification,
a reply or a CNode (`passiveKindAt`). -/
def passiveKernelObject : Option KernelObject → Prop
  | some (.endpoint _) => True
  | some (.notification _) => True
  | some (.reply _) => True
  | some (.cnode _) => True
  | _ => False

theorem passiveKindAt_iff (st : SystemState) (x : SeLe4n.ObjId) :
    passiveKindAt st x = true ↔ passiveKernelObject st.objects[x]? := by
  unfold passiveKindAt SystemState.getObjectType?
  cases st.objects[x]? with
  | none => simp [passiveKernelObject]
  | some o => cases o <;> simp [passiveKernelObject, KernelObject.objectType]

/-- **The kinds the retire erases**, read off a key: a passive kind, a thread
or a scheduling context (`erasableKindAt`). -/
def erasableKernelObject : Option KernelObject → Prop
  | some (.endpoint _) => True
  | some (.notification _) => True
  | some (.reply _) => True
  | some (.cnode _) => True
  | some (.tcb _) => True
  | some (.schedContext _) => True
  | _ => False

theorem erasableKindAt_iff (st : SystemState) (x : SeLe4n.ObjId) :
    erasableKindAt st x = true ↔ erasableKernelObject st.objects[x]? := by
  unfold erasableKindAt passiveKindAt schedulingKindAt SystemState.getObjectType?
  cases st.objects[x]? with
  | none => simp [erasableKernelObject]
  | some o => cases o <;> simp [erasableKernelObject, KernelObject.objectType]

theorem passiveKernelObject.erasable {o : Option KernelObject} (h : passiveKernelObject o) :
    erasableKernelObject o := by
  rcases o with _ | o
  · exact h
  · cases o <;> first | trivial | exact h

/-- An erasable object is not carved. -/
theorem not_carvedAt_of_erasable {st : SystemState} {x : SeLe4n.ObjId}
    (h : erasableKernelObject st.objects[x]?) : ¬ carvedAt st x := by
  rintro (⟨f, hf⟩ | ⟨u, hu⟩ | ⟨r, hr⟩ | ⟨p, hp⟩)
  · rw [hf] at h; exact h
  · rw [hu] at h; exact h
  · rw [hr] at h; exact h
  · rw [hp] at h; exact h

/-- A passive object is not carved. -/
theorem not_carvedAt_of_passive {st : SystemState} {x : SeLe4n.ObjId}
    (h : passiveKernelObject st.objects[x]?) : ¬ carvedAt st x := by
  rintro (⟨f, hf⟩ | ⟨u, hu⟩ | ⟨r, hr⟩ | ⟨p, hp⟩)
  · rw [hf] at h; exact h
  · rw [hu] at h; exact h
  · rw [hr] at h; exact h
  · rw [hp] at h; exact h

theorem eraseRetiredObject_of_not (st : SystemState) (x : SeLe4n.ObjId)
    (h : ¬ erasableKernelObject st.objects[x]?) : eraseRetiredObject st x = st := by
  rw [eraseRetiredObject_eq]
  rw [if_neg (fun h' => h ((erasableKindAt_iff st x).mp h'))]

/-- **The passive erase's frame**: the table keeps its invariant and headroom;
the scheduler, the machine, the tree and the ASID table are unchanged; every
key but `x` holds what it held, and `x` too unless it held a passive object,
which is now absent. -/
theorem eraseRetiredObject_frame (st : SystemState) (x : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hSz : st.objects.size < st.objects.capacity) :
    (eraseRetiredObject st x).objects.invExt ∧
    (eraseRetiredObject st x).objects.size < (eraseRetiredObject st x).objects.capacity ∧
    (eraseRetiredObject st x).scheduler = st.scheduler ∧
    (eraseRetiredObject st x).machine = st.machine ∧
    (eraseRetiredObject st x).cdt = st.cdt ∧
    (eraseRetiredObject st x).asidTable = st.asidTable ∧
    (∀ oid : SeLe4n.ObjId, oid ≠ x → (eraseRetiredObject st x).objects[oid]? = st.objects[oid]?) ∧
    ((eraseRetiredObject st x).objects[x]? = st.objects[x]? ∨
      (erasableKernelObject st.objects[x]? ∧ (eraseRetiredObject st x).objects[x]? = none)) := by
  by_cases hP : erasableKernelObject st.objects[x]?
  · have hE : eraseRetiredObject st x =
        { st with
          objects := st.objects.erase x
          objectIndex := st.objectIndex.filter (· != x)
          objectIndexSet := st.objectIndexSet.erase x
          lifecycle := { objectTypes := st.lifecycle.objectTypes.erase x } } := by
      rw [eraseRetiredObject_eq, if_pos ((erasableKindAt_iff st x).mpr hP)]
    rw [hE]
    refine ⟨SeLe4n.Kernel.RobinHood.RHTable.erase_preserves_invExt st.objects x hInv hSz,
      SeLe4n.Kernel.RobinHood.RHTable.erase_size_lt_capacity st.objects x hSz, rfl, rfl, rfl, rfl,
      fun oid hK => ?_,
      .inr ⟨hP, SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_self st.objects x hInv⟩⟩
    have hNe : ¬(x == oid) = true := by intro h; exact hK (eq_of_beq h).symm
    exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_ne st.objects x oid hNe hInv hSz
  · rw [eraseRetiredObject_of_not st x hP]
    exact ⟨hInv, hSz, rfl, rfl, rfl, rfl, fun _ _ => rfl, .inl rfl⟩

/-- **What a retire leaves of an untyped at `oid`**, `x`'s children being
`kids`: the same region, its child list its own or its own with `kids` adopted
in place of `x` (`childListAdopt`), and the untyped itself unchanged unless it
recorded `x` or is one of `kids`. -/
def untypedRetireStep (kids : List UntypedChild) (x oid : SeLe4n.ObjId) (U U' : UntypedObject) : Prop :=
  U'.regionBase = U.regionBase ∧ U'.regionSize = U.regionSize ∧ U'.isDevice = U.isDevice ∧
    (U'.children = U.children ∨ U'.children = childListAdopt U.children x kids) ∧
    (U' = U ∨ childListRecords U.children x = true ∨ ∃ c ∈ kids, c.objId = oid)

/-- **A final-delete retire write** of `x`: every key holds what it held, but
`x`, a carved or passive object now absent, and untypeds other than `x` that
record `x` or are its children, rewritten by the splice (`untypedRetireStep`). -/
def finalRetireWrite (st st' : SystemState) (x : SeLe4n.ObjId) : Prop :=
  ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
    (oid = x ∧ (carvedAt st oid ∨ erasableKernelObject st.objects[oid]?) ∧
      st'.objects[oid]? = none) ∨
    ∃ U U', oid ≠ x ∧ st.objects[oid]? = some (KernelObject.untyped U) ∧
      st'.objects[oid]? = some (KernelObject.untyped U') ∧
      untypedRetireStep (retiredChildren st x) x oid U U'

/-- **A write that keeps `x`, or erases a kernel object there, keeps the
children `x` records**: an erasable object is no untyped. -/
theorem retiredChildren_of_write {st st0 : SystemState} {x : SeLe4n.ObjId}
    (h : st0.objects[x]? = st.objects[x]? ∨
      (erasableKernelObject st.objects[x]? ∧ st0.objects[x]? = none)) :
    retiredChildren st0 x = retiredChildren st x := by
  unfold retiredChildren SystemState.getUntyped?
  rcases h with e | ⟨hp, hn⟩
  · rw [e]
  · rw [hn]; revert hp
    cases st.objects[x]? with
    | none => intro _; rfl
    | some o => cases o <;> first | (intro _; rfl) | (intro h; simp [erasableKernelObject] at h)

/-- **A retire write keeps every key a predicate admits**, when the predicate
admits neither `x`, nor any untyped recording it, nor any child it records. -/
theorem finalRetireWrite.objects_of_excluded {st st' : SystemState} {x : SeLe4n.ObjId}
    (F : finalRetireWrite st st' x) (p : SeLe4n.ObjId → Bool) (hx : p x = false)
    (hU : ∀ w, untypedRecordsChild st w x = true → p w = false)
    (hK : ∀ y, untypedRecordsChild st x y = true → p y = false)
    (o : SeLe4n.ObjId) (ho : p o = true) : st'.objects[o]? = st.objects[o]? := by
  rcases F o with e | ⟨hxo, -, -⟩ | ⟨U, U', -, hU0, hU1, -, -, -, -, hk⟩
  · exact e
  · subst hxo; rw [hx] at ho; cases ho
  · rcases hk with rfl | hr | ⟨c, hc, he⟩
    · rw [hU0, hU1]
    · have : untypedRecordsChild st o x = true := by
        unfold untypedRecordsChild; rw [(SystemState.getUntyped?_eq_some_iff st o U).mpr hU0]; exact hr
      rw [hU o this] at ho; cases ho
    · rw [← he, hK _ (mem_retiredChildren hc)] at ho; cases ho

/-- **A retire write records no child but those it adopts**: an untyped that
records `o` after it recorded `o` before, or recorded `x`, which recorded `o`. -/
theorem finalRetireWrite.recordsChild {st st' : SystemState} {x : SeLe4n.ObjId}
    (F : finalRetireWrite st st' x) {w o : SeLe4n.ObjId}
    (h : untypedRecordsChild st' w o = true) :
    untypedRecordsChild st w o = true ∨
      (untypedRecordsChild st w x = true ∧ untypedRecordsChild st x o = true) := by
  unfold untypedRecordsChild at h
  cases hA : st'.getUntyped? w with
  | none => rw [hA] at h; cases h
  | some U' =>
    rw [hA] at h
    dsimp only at h
    have hA' := (SystemState.getUntyped?_eq_some_iff _ w U').mp hA
    rcases F w with e | ⟨-, -, hn⟩ | ⟨U, U'', -, hU0, hU1, -, -, -, hch, -⟩
    · left; unfold untypedRecordsChild
      rw [e] at hA'; rw [(SystemState.getUntyped?_eq_some_iff st w U').mpr hA']; exact h
    · rw [hn] at hA'; cases hA'
    · rw [hU1] at hA'; cases hA'
      have hw : st.getUntyped? w = some U := (SystemState.getUntyped?_eq_some_iff st w U).mpr hU0
      obtain ⟨ch, hm, he⟩ := (childListRecords_iff _ _).mp h
      rcases hch with e | e
      · left; unfold untypedRecordsChild; rw [hw]
        exact (childListRecords_iff _ _).mpr ⟨ch, e ▸ hm, he⟩
      · rw [e] at hm
        rcases (mem_childListAdopt hm).2 with hm' | ⟨hr, c0, hc0, he0⟩
        · left; unfold untypedRecordsChild; rw [hw]
          exact (childListRecords_iff _ _).mpr ⟨ch, hm', he⟩
        · right
          refine ⟨by unfold untypedRecordsChild; rw [hw]; exact hr, ?_⟩
          have := mem_retiredChildren hc0
          rw [he0, he] at this; exact this

/-- **The passive erase as a write**: every key holds what it held, but `x`,
a passive object now absent. -/
theorem eraseRetiredObject_write (st : SystemState) (x : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hSz : st.objects.size < st.objects.capacity) (oid : SeLe4n.ObjId) :
    (eraseRetiredObject st x).objects[oid]? = st.objects[oid]? ∨
      (oid = x ∧ erasableKernelObject st.objects[oid]? ∧ (eraseRetiredObject st x).objects[oid]? = none) := by
  obtain ⟨-, -, -, -, -, -, hNe, hAt⟩ := eraseRetiredObject_frame st x hInv hSz
  by_cases hK : oid = x
  · subst hK
    rcases hAt with e | ⟨hp, hn⟩
    · exact .inl e
    · exact .inr ⟨rfl, hp, hn⟩
  · exact .inl (hNe oid hK)

/-- **A passive erase followed by a retire write is a retire write.** -/
theorem finalRetireWrite.of_passive {st st0 st' : SystemState} {x : SeLe4n.ObjId}
    (h0 : ∀ oid : SeLe4n.ObjId, st0.objects[oid]? = st.objects[oid]? ∨
      (oid = x ∧ erasableKernelObject st.objects[oid]? ∧ st0.objects[oid]? = none))
    (h : finalRetireWrite st0 st' x) : finalRetireWrite st st' x := by
  intro oid
  rcases h oid with e | ⟨hx, hcp, hn⟩ | ⟨U, U', hx, hU, hU', hS⟩
  · rcases h0 oid with e0 | ⟨hx, hp, hn0⟩
    · exact .inl (e.trans e0)
    · exact .inr (.inl ⟨hx, .inr hp, e.trans hn0⟩)
  · refine .inr (.inl ⟨hx, ?_, hn⟩)
    rcases h0 oid with e0 | ⟨-, -, hn0⟩
    · unfold carvedAt at hcp ⊢; rw [e0] at hcp; exact hcp
    · exfalso
      rcases hcp with (⟨f, hf⟩ | ⟨u, hu⟩ | ⟨r, hr⟩ | ⟨p, hp⟩) | hp
      · rw [hn0] at hf; cases hf
      · rw [hn0] at hu; cases hu
      · rw [hn0] at hr; cases hr
      · rw [hn0] at hp; cases hp
      · rw [hn0] at hp; exact hp
  · have hK : retiredChildren st0 x = retiredChildren st x := retiredChildren_of_write
      ((h0 x).imp_right fun ⟨_, hp, hn⟩ => ⟨hp, hn⟩)
    rcases h0 oid with e0 | ⟨-, -, hn0⟩
    · exact .inr (.inr ⟨U, U', hx, e0 ▸ hU, hU', hK ▸ hS⟩)
    · rw [hn0] at hU; cases hU

/-- **The recorded retire's frame**: the table keeps its invariant; the
scheduler, the machine and the tree are unchanged; and the objects change by a
final-delete retire write of `x`. -/
theorem retireRecordedObject_frame (ec : Concurrency.CoreId) (recorder : Nat) (x : SeLe4n.ObjId)
    (st : SystemState) (hInv : st.objects.invExt) (hSz : st.objects.size < st.objects.capacity) :
    (retireRecordedObject ec recorder x st).objects.invExt ∧
    (retireRecordedObject ec recorder x st).scheduler = st.scheduler ∧
    (retireRecordedObject ec recorder x st).machine = st.machine ∧
    (retireRecordedObject ec recorder x st).cdt = st.cdt ∧
    finalRetireWrite st (retireRecordedObject ec recorder x st) x := by
  unfold retireRecordedObject
  dsimp only
  obtain ⟨i1, room1, s1, m1, c1, w1⟩ := retireUnrecord_frame recorder x st hInv hSz
  generalize retireUnrecord recorder x st = st1 at i1 room1 s1 m1 c1 w1
  obtain ⟨i2, -, -, -, -⟩ := retireCarvedObject_frame st1 x i1 room1
  obtain ⟨s2, m2, c2⟩ := retireCarvedObject_scheduler_machine_cdt st1 x
  have hW : finalRetireWrite st (retireCarvedObject st1 x) x := by
    intro oid
    by_cases hK : oid = x
    · subst hK
      rcases (retireCarvedObject_frame st1 oid i1 room1).2.2.2.1 oid with e | ⟨hc, hn⟩
      · rw [e]
        rcases w1 oid with e1 | ⟨U, U', hU, hU', -⟩
        · exact .inl e1
        · exfalso
          have := (retireCarvedObject_frame st1 oid i1 room1).2.2.2.2 (.inr (.inr (.inl ⟨U', hU'⟩)))
          rw [e, hU'] at this; cases this
      · refine .inr (.inl ⟨rfl, .inl ?_, hn⟩)
        rcases w1 oid with e1 | ⟨U, U', hU, -⟩
        · unfold carvedAt at hc ⊢; rw [← e1]; exact hc
        · exact .inr (.inl ⟨U, hU⟩)
    · rw [retireCarvedObject_objects_ne st1 x oid hK i1 room1]
      rcases w1 oid with e1 | ⟨U, U', hU, hU', h⟩
      · exact .inl e1
      · exact .inr (.inr ⟨U, U', hK, hU, hU', h⟩)
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
  · exact hAll _ ((asidReleaseRound_objects _ _ _))
      ((asidReleaseRound_scheduler _ _ _))
      ((asidReleaseRound_machine _ _ _))
      ((asidReleaseRound_cdt _ _ _))
  · exact hAll _ rfl rfl rfl rfl

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
    split
    · obtain ⟨i0, room0, s0, m0, c0, -, -, -⟩ := eraseRetiredObject_frame st _ hInv hSz
      obtain ⟨i, s, m, c, w⟩ := retireRecordedObject_frame ec recorder _ _ i0 room0
      exact ⟨i, s.trans s0, m.trans m0, c.trans c0,
        finalRetireWrite.of_passive (eraseRetiredObject_write st _ hInv hSz) w⟩
    · exact ⟨hInv, rfl, rfl, rfl, fun _ => .inl rfl⟩
  · exact ⟨hInv, rfl, rfl, rfl, fun _ => .inl rfl⟩

/-- **The object kinds a final-delete retire touches without erasing them as a
thread or a scheduling context**: the memory kinds (`memoryKindOrAbsent`) and the
four passive kinds.  None is a TCB or a scheduling context, so none feeds the
scheduler; the one thread or context a retire can take out is erased whole,
detached first (`retireFinalObject_touched`). -/
def retireTouched : Option KernelObject → Prop
  | some (.tcb _) => False
  | some (.schedContext _) => False
  | _ => True

/-- **A thread or a scheduling context**, read off a key (`schedulingKindAt`). -/
def schedulingKernelObject : Option KernelObject → Prop
  | some (.tcb _) => True
  | some (.schedContext _) => True
  | _ => False

theorem schedulingKindAt_iff (st : SystemState) (x : SeLe4n.ObjId) :
    schedulingKindAt st x = true ↔ schedulingKernelObject st.objects[x]? := by
  unfold schedulingKindAt SystemState.getObjectType?
  cases st.objects[x]? with
  | none => simp [schedulingKernelObject]
  | some o => cases o <;> simp [schedulingKernelObject, KernelObject.objectType]

/-- **A retire write touches only what a retire may touch**: every key holds
what it held, or a kind `retireTouched` admits on both sides, or it is the
target, a thread or a scheduling context now absent. -/
theorem finalRetireWrite.touched {st st' : SystemState} {x : SeLe4n.ObjId}
    (h : finalRetireWrite st st' x) (oid : SeLe4n.ObjId) :
    st'.objects[oid]? = st.objects[oid]? ∨
      (retireTouched st.objects[oid]? ∧ retireTouched st'.objects[oid]?) ∨
      (oid = x ∧ st'.objects[oid]? = none ∧ schedulingKernelObject st.objects[oid]?) := by
  rcases h oid with e | ⟨hx, hcp, hn⟩ | ⟨U, U', -, hU, hU', -⟩
  · exact .inl e
  · rcases hcp with (⟨f, hf⟩ | ⟨u, hu⟩ | ⟨r, hr⟩ | ⟨p, hp⟩) | hp
    · exact .inr (.inl ⟨by rw [hf]; trivial, by rw [hn]; trivial⟩)
    · exact .inr (.inl ⟨by rw [hu]; trivial, by rw [hn]; trivial⟩)
    · exact .inr (.inl ⟨by rw [hr]; trivial, by rw [hn]; trivial⟩)
    · exact .inr (.inl ⟨by rw [hp]; trivial, by rw [hn]; trivial⟩)
    · revert hp
      cases hO : st.objects[oid]? with
      | none => intro _; exact .inr (.inl ⟨trivial, by rw [hn]; trivial⟩)
      | some o =>
        cases o <;> first
          | (intro _; exact .inr (.inl ⟨trivial, by rw [hn]; trivial⟩))
          | (intro _; exact .inr (.inr ⟨hx, hn, trivial⟩))
          | (intro h; simp [erasableKernelObject] at h)
  · rw [hU, hU']; exact .inr (.inl ⟨trivial, trivial⟩)

/-- **The passive erase moves no record**: it erases no untyped. -/
theorem eraseRetiredObject_untypedRecordsChild (st : SystemState) (x : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hSz : st.objects.size < st.objects.capacity) (w y : SeLe4n.ObjId) :
    untypedRecordsChild (eraseRetiredObject st x) w y = untypedRecordsChild st w y := by
  unfold untypedRecordsChild SystemState.getUntyped?
  rcases eraseRetiredObject_write st x hInv hSz w with e | ⟨-, hp, hn⟩
  · rw [e]
  · rw [hn]; revert hp
    cases st.objects[w]? with
    | none => intro _; rfl
    | some o => cases o <;> first | (intro _; rfl) | (intro h; simp [erasableKernelObject] at h)

/-- **After the recorded retire no untyped records `x`**, when the recorder
word answers truly and at most one untyped recorded `x`: the recorder's records
of `x` are replaced by `x`'s children, and no other untyped recorded `x`.  Nor
is `x` an untyped after (`retireRecordedObject_target_gone`). -/
theorem retireRecordedObject_unrecorded (ec : Concurrency.CoreId) (recorder : Nat) (x : SeLe4n.ObjId)
    (st : SystemState) (hInv : st.objects.invExt) (hSz : st.objects.size < st.objects.capacity)
    (hR1 : recorder ≠ 0 → untypedRecordsChild st (SeLe4n.ObjId.ofNat (recorder - 1)) x = true)
    (hR0 : recorder = 0 → ∀ w, untypedRecordsChild st w x = false)
    (hUniq : ∀ u v, untypedRecordsChild st u x = true → untypedRecordsChild st v x = true → u = v) :
    ∀ (u : SeLe4n.ObjId) (U' : UntypedObject),
      (retireRecordedObject ec recorder x st).objects[u]? = some (KernelObject.untyped U') →
      ∀ ch ∈ U'.children, ch.objId ≠ x := by
  have recU : ∀ {u U}, st.objects[u]? = some (KernelObject.untyped U) →
      childListRecords U.children x = true → untypedRecordsChild st u x = true := by
    intro u U hU hr
    unfold untypedRecordsChild; rw [(SystemState.getUntyped?_eq_some_iff st u U).mpr hU]; exact hr
  -- what the unrecord leaves: no untyped recording `x`
  have h1 : ∀ (u : SeLe4n.ObjId) (U' : UntypedObject),
      (retireUnrecord recorder x st).objects[u]? = some (KernelObject.untyped U') →
      ∀ ch ∈ U'.children, ch.objId ≠ x := by
    intro u U' hu ch hch hc
    obtain ⟨-, -, -, -, -, w1⟩ := retireUnrecord_frame recorder x st hInv hSz
    -- a pre-state untyped at `u` holding `U0`, with `U'.children` its own or adopted
    have hpre : ∃ U0, st.objects[u]? = some (KernelObject.untyped U0) ∧
        (U'.children = U0.children ∨
          U'.children = childListAdopt U0.children x (retiredChildren st x)) := by
      rcases w1 u with e | ⟨U0, U1, hU0, hU1, -, -, -, ch', -⟩
      · exact ⟨U', e ▸ hu, .inl rfl⟩
      · rw [hu] at hU1; cases hU1; exact ⟨U0, hU0, ch'⟩
    obtain ⟨U0, hU0, hch'⟩ := hpre
    rcases hch' with e | e
    · rw [e] at hch
      have hr := recU hU0 ((childListRecords_iff _ _).mpr ⟨ch, hch, hc⟩)
      by_cases h0 : recorder = 0
      · rw [hR0 h0 u] at hr; cases hr
      · have hw := hUniq _ _ hr (hR1 h0)
        subst hw
        obtain ⟨U2, hU2, hc2⟩ := retireUnrecord_recorder recorder x st hInv hSz h0 hU0
        rw [hu] at hU2; cases hU2
        rw [← e, hc2] at hch
        exact (mem_childListAdopt hch).1 hc
    · rw [e] at hch; exact (mem_childListAdopt hch).1 hc
  unfold retireRecordedObject
  dsimp only
  obtain ⟨i1, room1, -⟩ := retireUnrecord_frame recorder x st hInv hSz
  generalize retireUnrecord recorder x st = st1 at h1 i1 room1
  have hR : ∀ (u : SeLe4n.ObjId) (U' : UntypedObject),
      (retireCarvedObject st1 x).objects[u]? = some (KernelObject.untyped U') →
      ∀ ch ∈ U'.children, ch.objId ≠ x := by
    intro u U' hu
    by_cases hK : u = x
    · subst hK
      rcases (retireCarvedObject_frame st1 u i1 room1).2.2.2.1 u with e | ⟨-, hn⟩
      · rw [e] at hu; exact h1 u U' hu
      · rw [hn] at hu; cases hu
    · rw [retireCarvedObject_objects_ne st1 x u hK i1 room1] at hu
      exact h1 u U' hu
  split
  · intro u U' hu
    rw [asidReleaseRound_objects] at hu
    exact hR u U' hu
  · intro u U' hu
    exact hR u U' hu

/-- **After the recorded retire `x` is no untyped**: an untyped is carved, and
the carved retire takes it out. -/
theorem retireRecordedObject_target_gone (ec : Concurrency.CoreId) (recorder : Nat) (x : SeLe4n.ObjId)
    (st : SystemState) (hInv : st.objects.invExt) (hSz : st.objects.size < st.objects.capacity)
    (U' : UntypedObject) :
    (retireRecordedObject ec recorder x st).objects[x]? ≠ some (KernelObject.untyped U') := by
  unfold retireRecordedObject
  dsimp only
  obtain ⟨i1, room1, -⟩ := retireUnrecord_frame recorder x st hInv hSz
  generalize retireUnrecord recorder x st = st1 at i1 room1
  have hX : (retireCarvedObject st1 x).objects[x]? ≠ some (KernelObject.untyped U') := by
    intro hu
    rcases (retireCarvedObject_frame st1 x i1 room1).2.2.2.1 x with e | ⟨-, hn⟩
    · have := (retireCarvedObject_frame st1 x i1 room1).2.2.2.2 (.inr (.inr (.inl ⟨U', e ▸ hu⟩)))
      rw [hu] at this; cases this
    · rw [hn] at hu; cases hu
  split
  · rw [asidReleaseRound_objects]; exact hX
  · exact hX

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
    obtain ⟨hR1, hR0⟩ := hRec hT
    dsimp only
    split
    · right
      obtain ⟨i0, room0, -⟩ := eraseRetiredObject_frame st (SeLe4n.ObjId.ofNat (target - 1)) hInv hSz
      have hT0 := eraseRetiredObject_untypedRecordsChild st (SeLe4n.ObjId.ofNat (target - 1)) hInv hSz
      exact retireRecordedObject_unrecorded ec recorder _ _ i0 room0
        (fun h => (hT0 _ _).trans (hR1 h)) (fun h w => (hT0 _ _).trans (hR0 h w))
        (fun u v hu hv => hUniq u v ((hT0 _ _).symm.trans hu) ((hT0 _ _).symm.trans hv))
    · exact .inl rfl
  · exact .inl rfl

/-- **The retire writes only what its admission allows**: nothing, or the
admitted retire of its target (`finalRetireAdmitted`). -/
theorem retireFinalObject_admitted (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) :
    retireFinalObject ec target recorder st = st ∨
      finalRetireAdmitted st (SeLe4n.ObjId.ofNat (target - 1)) = true := by
  unfold retireFinalObject
  split
  · exact .inl rfl
  split
  · dsimp only
    split
    · next h => exact .inr h
    · exact .inl rfl
  · exact .inl rfl

/-- **After the retire its target is no untyped** — or the retire wrote
nothing. -/
theorem retireFinalObject_target_gone (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) :
    retireFinalObject ec target recorder st = st ∨
    ∀ U', (retireFinalObject ec target recorder st).objects[SeLe4n.ObjId.ofNat (target - 1)]? ≠
      some (KernelObject.untyped U') := by
  unfold retireFinalObject
  split
  · exact .inl rfl
  split
  · next hSz =>
    dsimp only
    split
    · obtain ⟨i0, room0, -⟩ := eraseRetiredObject_frame st (SeLe4n.ObjId.ofNat (target - 1)) hInv hSz
      exact .inr (retireRecordedObject_target_gone ec recorder _ _ i0 room0)
    · exact .inl rfl
  · exact .inl rfl

theorem passiveObjectRetirable_parts {st : SystemState} {x : SeLe4n.ObjId}
    (h : passiveObjectRetirable st x = true) :
    passiveObjectQuiescent st x = true ∧ st.tableBackLinksClear x = true := by
  unfold passiveObjectRetirable at h
  exact Bool.and_eq_true_iff.mp h

/-- An admitted retire of a passive object retires one `passiveObjectRetirable`
admits. -/
theorem finalRetireAdmitted.retirable {st : SystemState} {x : SeLe4n.ObjId}
    (h : finalRetireAdmitted st x = true) (hP : passiveKernelObject st.objects[x]?) :
    passiveObjectRetirable st x = true := by
  unfold finalRetireAdmitted at h
  rw [(passiveKindAt_iff st x).mpr hP] at h
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  exact h.1

/-- An admitted retire of a thread or a scheduling context retires one
`schedulingObjectRetirable` admits. -/
theorem finalRetireAdmitted.schedulingRetirable {st : SystemState} {x : SeLe4n.ObjId}
    (h : finalRetireAdmitted st x = true) (hS : schedulingKindAt st x = true) :
    schedulingObjectRetirable st x = true := by
  unfold finalRetireAdmitted at h
  rw [hS] at h
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  exact h.2

/-- A CNode whose occupancy links head nowhere answers every lookup empty
(`CNode.occ_agree`). -/
theorem CNode.lookup_none_of_occHead_zero {cn : CNode} (h : (cn.occHead == 0) = true)
    (s : SeLe4n.Slot) : cn.lookup s = none := by
  obtain ⟨L, hE⟩ := cn.occ_agree
  have h0 : cn.occHead = 0 := by simpa using h
  rw [h0] at hE
  have hN := hE.none_of_head_zero s.toNat
  rw [CNode.lookup_eq_lookupCells]
  unfold CNode.lookupCells slotArrayGet
  split
  · next hs =>
    unfold SlotOccupancy.occupied at hN
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs] at hN
    simpa using hN
  · rfl

/-- **A quiescent passive object holds no capability**: only a CNode has slots
among the passive kinds, and a quiescent one has every slot empty. -/
theorem passiveObjectQuiescent.slotCap {st : SystemState} {x : SeLe4n.ObjId}
    (h : passiveObjectQuiescent st x = true) (o : KernelObject) (hO : st.objects[x]? = some o)
    (s : SeLe4n.Slot) : o.slotCap s = none := by
  unfold passiveObjectQuiescent SystemState.getObject? at h
  rw [hO] at h
  cases o with
  | cnode cn => exact CNode.lookup_none_of_occHead_zero h s
  | _ => first | rfl | (simp at h)

/-- **A quiescent endpoint's own links**: both queues empty. -/
theorem passiveObjectQuiescent_endpoint {st : SystemState} {x : SeLe4n.ObjId} {ep : Endpoint}
    (h : passiveObjectQuiescent st x = true) (hE : st.objects[x]? = some (.endpoint ep)) :
    ep.sendQ.head = none ∧ ep.receiveQ.head = none := by
  unfold passiveObjectQuiescent at h
  rw [SystemState.getObject?_eq_getElem, hE] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  simp only [Endpoint.sendQ, Endpoint.receiveQ, h.1, h.2]
  exact ⟨rfl, rfl⟩

/-- **A quiescent notification's own links**: no waiter and no bound thread. -/
theorem passiveObjectQuiescent_notification {st : SystemState} {x : SeLe4n.ObjId}
    {n : Notification} (h : passiveObjectQuiescent st x = true)
    (hN : st.objects[x]? = some (.notification n)) :
    n.waitHead = none ∧ n.boundTCBCode = 0 := by
  unfold passiveObjectQuiescent at h
  rw [SystemState.getObject?_eq_getElem, hN] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  simp only [Notification.waitHead, h.1]
  exact ⟨rfl, h.2⟩

/-- **A quiescent reply's own links**: no caller, no live stash (the receiver it
records stashes it no more), and no stack link. -/
theorem passiveObjectQuiescent_reply {st : SystemState} {x : SeLe4n.ObjId} {r : Reply}
    (h : passiveObjectQuiescent st x = true) (hR : st.objects[x]? = some (.reply r)) :
    r.callerCode = 0 ∧ st.replyStashedAt ⟨x.val⟩ r = false ∧ r.prev = none ∧ r.next = none := by
  unfold passiveObjectQuiescent at h
  rw [SystemState.getObject?_eq_getElem, hR] at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Option.isNone_iff_eq_none] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- **What the retire guard reads of a thread it admits**: the thread stored
under its own id, no idle thread, quiescent and held by no core. -/
theorem threadRetirable_parts {st : SystemState} {x : SeLe4n.ObjId}
    (h : threadRetirable st x = true) :
    ∃ t, st.objects[x]? = some (.tcb t) ∧ t.tid.val = x.val ∧ isIdleThreadId t.tid = false ∧
      threadQuiescent t = true ∧ threadHeldOnSomeCore st t.tid = false := by
  unfold threadRetirable SystemState.getObject? at h
  cases hO : st.objects[x]? with
  | none => rw [hO] at h; cases h
  | some o =>
    rw [hO] at h
    cases o with
    | tcb t =>
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      exact ⟨t, rfl, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
    | _ => cases h

/-- **A retired thread runs on no core**: the retire admits a thread only when
no core's committed current slot names it, so a final delete of a thread another
core was running retires it only once its finalisation has vacated that core's
slot.  What the core's hardware still runs there is the remote-core stall's to
settle before the delete returns (`Concurrency.stallChangedCores`, run by the
syscall entry after its commit against these same current slots). -/
theorem threadRetirable_currentNowhere {st : SystemState} {x : SeLe4n.ObjId}
    (h : threadRetirable st x = true) (c : Concurrency.CoreId) :
    st.scheduler.currentOnCore c ≠ some ⟨x.val⟩ := by
  obtain ⟨t, -, hTid, -, -, hHeld⟩ := threadRetirable_parts h
  intro hCur
  have hId : t.tid = ⟨x.val⟩ := by cases hT : t.tid; simp_all
  have hNot : threadCurrentOnSomeCore st t.tid = false := by
    unfold threadHeldOnSomeCore at hHeld
    simp only [Bool.or_eq_false_iff] at hHeld
    exact hHeld.1.1
  rw [hId] at hNot
  have := (threadCurrentOnSomeCore_iff st ⟨x.val⟩).mpr ⟨c, hCur⟩
  rw [hNot] at this; cases this

/-- **What the retire guard reads of a scheduling context it admits.** -/
theorem schedContextRetirable_parts {st : SystemState} {x : SeLe4n.ObjId}
    (h : schedContextRetirable st x = true) :
    ∃ sc, st.objects[x]? = some (.schedContext sc) ∧ sc.boundThreadCode = 0 ∧
      sc.donationOrigin = none ∧ sc.scReply = none ∧ sc.releaseCoreCode = 0 ∧
      sc.yieldFromCode = 0 := by
  unfold schedContextRetirable SystemState.getObject? at h
  cases hO : st.objects[x]? with
  | none => rw [hO] at h; cases h
  | some o =>
    rw [hO] at h
    cases o with
    | schedContext sc =>
      simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
      exact ⟨sc, rfl, h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
    | _ => cases h

/-- A thread the scan admits is the one `threadRetirable` reads. -/
theorem schedulingObjectRetirable_tcb {st : SystemState} {x : SeLe4n.ObjId} {t : TCB}
    (h : schedulingObjectRetirable st x = true) (hT : st.objects[x]? = some (.tcb t)) :
    threadRetirable st x = true := by
  unfold schedulingObjectRetirable at h
  have : schedContextRetirable st x = false := by
    unfold schedContextRetirable SystemState.getObject?; rw [hT]
  rw [this, Bool.or_false] at h; exact h

/-- A scheduling context the scan admits is the one `schedContextRetirable`
reads. -/
theorem schedulingObjectRetirable_schedContext {st : SystemState} {x : SeLe4n.ObjId}
    {sc : SchedContext} (h : schedulingObjectRetirable st x = true)
    (hS : st.objects[x]? = some (.schedContext sc)) :
    schedContextRetirable st x = true := by
  unfold schedulingObjectRetirable at h
  have : threadRetirable st x = false := by
    unfold threadRetirable SystemState.getObject?; rw [hS]
  rw [this, Bool.false_or] at h; exact h

/-- **A quiescent thread holds no capability**: both space slots are empty. -/
theorem threadQuiescent.slotCap {t : TCB} (h : threadQuiescent t = true) (s : SeLe4n.Slot) :
    (KernelObject.tcb t).slotCap s = none := by
  unfold threadQuiescent threadLinksQuiescent at h
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  have h0 := h.1
  have h1 := h.2
  show t.spaceSlotCap s = none
  unfold TCB.spaceSlotCap
  split
  · next hs =>
    have : s.toNat = 0 ∨ s.toNat = 1 := by omega
    rcases this with e | e
    · simp only [e]; exact h0.2
    · simp only [e]; exact h1
  · rfl

/-- **An admitted retire erases an object that holds no capability.** -/
theorem finalRetireAdmitted.slotCap {st : SystemState} {x : SeLe4n.ObjId}
    (hAdm : finalRetireAdmitted st x = true) (hp : erasableKernelObject st.objects[x]?)
    (o : KernelObject) (hO : st.objects[x]? = some o) (s : SeLe4n.Slot) : o.slotCap s = none := by
  cases o with
  | tcb t =>
    have hS : schedulingKindAt st x = true := (schedulingKindAt_iff st x).mpr (by rw [hO]; trivial)
    obtain ⟨t', hT', -, -, hQ, -⟩ :=
      threadRetirable_parts (schedulingObjectRetirable_tcb (finalRetireAdmitted.schedulingRetirable hAdm hS) hO)
    rw [hO] at hT'; cases hT'
    exact threadQuiescent.slotCap hQ s
  | schedContext _ => rfl
  | _ =>
    have hP : passiveKernelObject st.objects[x]? := by
      rw [hO] at hp ⊢; exact hp
    exact passiveObjectQuiescent.slotCap
      (passiveObjectRetirable_parts (finalRetireAdmitted.retirable hAdm hP)).1 _ hO s

/-- **What the retire touches, key by key**: what it held, or a kind
`retireTouched` admits on both sides, or a thread or scheduling context the
retire admitted as detached (`schedulingObjectRetirable`), now absent. -/
theorem retireFinalObject_touched (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) (oid : SeLe4n.ObjId) :
    (retireFinalObject ec target recorder st).objects[oid]? = st.objects[oid]? ∨
      (retireTouched st.objects[oid]? ∧
        retireTouched (retireFinalObject ec target recorder st).objects[oid]?) ∨
      ((retireFinalObject ec target recorder st).objects[oid]? = none ∧
        schedulingKernelObject st.objects[oid]? ∧ schedulingObjectRetirable st oid = true) := by
  rcases retireFinalObject_admitted ec target recorder st with hE | hAdm
  · rw [hE]; exact .inl rfl
  rcases ((retireFinalObject_frame ec target recorder st hInv).2.2.2.2).touched oid with
    e | t | ⟨hx, hn, hS⟩
  · exact .inl e
  · exact .inr (.inl t)
  · subst hx
    exact .inr (.inr ⟨hn, hS,
      finalRetireAdmitted.schedulingRetirable hAdm ((schedulingKindAt_iff st _).mpr hS)⟩)

/-- **What a quiescent thread's codes are**, flattened in the order
`threadQuiescent` reads them. -/
theorem threadQuiescent_codes {t : TCB} (h : threadQuiescent t = true) :
    t.threadState = .Inactive ∧ t.ipcStateCode = 0 ∧ t.ipcObjectCode = 0 ∧
    t.pendingMessage = none ∧ t.queueNextCode = 0 ∧ t.queuePrevCode = 0 ∧
    t.queuePPrevCode = 0 ∧ t.ntfnNextCode = 0 ∧ t.ntfnPrevCode = 0 ∧ t.runCoreCode = 0 ∧
    t.replyWaiterNextCode = 0 ∧ t.replyWaiterPrevCode = 0 ∧
    t.replyWaitersHeadCode = 0 ∧ t.scBindingScCode = 0 ∧ t.scBindingOwnerCode = 0 ∧
    t.boundNotificationCode = 0 ∧ t.replyObjectCode = 0 ∧ t.pendingReceiveReplyCode = 0 ∧
    t.timeoutBudget = none ∧ t.yieldToCode = 0 ∧ t.spaceCells[0] = none ∧
    t.spaceCells[1] = none := by
  unfold threadQuiescent threadLinksQuiescent at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none, and_assoc] at h
  exact h

/-- A quiescent thread is ready: both of its state words are zero. -/
theorem threadQuiescent_ipcState {t : TCB} (h : threadQuiescent t = true) :
    t.ipcState = .ready := by
  obtain ⟨-, h1, h2, -⟩ := threadQuiescent_codes h
  unfold TCB.ipcState; rw [h1, h2]; rfl

/-- A quiescent thread links to no queue successor. -/
theorem threadQuiescent_queueNext {t : TCB} (h : threadQuiescent t = true) :
    t.queueNext = none := by
  obtain ⟨-, -, -, -, h1, -⟩ := threadQuiescent_codes h
  unfold TCB.queueNext; rw [h1]; rfl

/-- The passive erase of a passive object leaves its key empty. -/
theorem eraseRetiredObject_self {st : SystemState} {x : SeLe4n.ObjId}
    (hP : erasableKernelObject st.objects[x]?) (hInv : st.objects.invExt) :
    (eraseRetiredObject st x).objects[x]? = none := by
  rw [eraseRetiredObject_eq]
  rw [if_pos ((erasableKindAt_iff st x).mpr hP)]
  exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_self st.objects x hInv

/-- **After the passive erase no passive object stands at `x`.** -/
theorem eraseRetiredObject_not_passive (st : SystemState) (x : SeLe4n.ObjId)
    (hInv : st.objects.invExt) : ¬ erasableKernelObject (eraseRetiredObject st x).objects[x]? := by
  by_cases hP0 : erasableKernelObject st.objects[x]?
  · rw [eraseRetiredObject_self hP0 hInv]; exact fun h => h
  · rw [eraseRetiredObject_of_not st x hP0]; exact hP0

/-- **A retire write at a key holding no passive object touches only the memory
kinds.** -/
theorem finalRetireWrite.memoryKindOrAbsent {st st' : SystemState} {x : SeLe4n.ObjId}
    (h : finalRetireWrite st st' x) (hNP : ¬ erasableKernelObject st.objects[x]?)
    (oid : SeLe4n.ObjId) :
    st'.objects[oid]? = st.objects[oid]? ∨
      (memoryKindOrAbsent st.objects[oid]? ∧ memoryKindOrAbsent st'.objects[oid]?) := by
  rcases h oid with e | ⟨hx, hcp, hn⟩ | ⟨U, U', -, hU, hU', -⟩
  · exact .inl e
  · refine .inr ⟨?_, by rw [hn]; trivial⟩
    rcases hcp with (⟨f, hf⟩ | ⟨u, hu⟩ | ⟨r, hr⟩ | ⟨p, hp⟩) | hp
    · rw [hf]; trivial
    · rw [hu]; trivial
    · rw [hr]; trivial
    · rw [hp]; trivial
    · subst hx; exact absurd hp hNP
  · rw [hU, hU']; exact .inr ⟨trivial, trivial⟩

/-- **The retire, decomposed**: nothing, or — with a nonzero target, headroom
and the retire admitted — the passive erase followed by the recorded retire. -/
theorem retireFinalObject_cases (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) :
    retireFinalObject ec target recorder st = st ∨
      (st.objects.size < st.objects.capacity ∧
        finalRetireAdmitted st (SeLe4n.ObjId.ofNat (target - 1)) = true ∧
        retireFinalObject ec target recorder st =
          retireRecordedObject ec recorder (SeLe4n.ObjId.ofNat (target - 1))
            (eraseRetiredObject st (SeLe4n.ObjId.ofNat (target - 1)))) := by
  unfold retireFinalObject
  split
  · exact .inl rfl
  split
  · next hSz =>
    dsimp only
    split
    · next h => exact .inr ⟨hSz, h, rfl⟩
    · exact .inl rfl
  · exact .inl rfl

/-- **What the retire leaves at each key**: what it held, or — where it held no
thread and no capability — nothing or an untyped. -/
theorem retireFinalObject_key (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) (oid : SeLe4n.ObjId) :
    (retireFinalObject ec target recorder st).objects[oid]? = st.objects[oid]? ∨
      ((∀ o, st.objects[oid]? = some o → ∀ s, o.slotCap s = none) ∧
        (∀ t, st.objects[oid]? = some (.tcb t) → threadRetirable st oid = true) ∧
        ((retireFinalObject ec target recorder st).objects[oid]? = none ∨
          ∃ U, (retireFinalObject ec target recorder st).objects[oid]? = some (.untyped U))) := by
  rcases retireFinalObject_admitted ec target recorder st with hE | hAdm
  · rw [hE]; exact .inl rfl
  have hW := (retireFinalObject_frame ec target recorder st hInv).2.2.2.2
  generalize retireFinalObject ec target recorder st = st' at hW ⊢
  rcases hW oid with e | ⟨hxo, hcp, hn⟩ | ⟨U, U', -, hU, hU', -⟩
  · exact .inl e
  · refine .inr ⟨?_, ?_, .inl hn⟩
    · intro o hO s
      rcases hcp with (⟨f, hf⟩ | ⟨u, hu⟩ | ⟨r, hr⟩ | ⟨p, hp⟩) | hp
      · rw [hf] at hO; cases hO; rfl
      · rw [hu] at hO; cases hO; rfl
      · rw [hr] at hO; cases hO; rfl
      · rw [hp] at hO; cases hO; rfl
      · subst hxo
        exact finalRetireAdmitted.slotCap hAdm hp o hO s
    · intro t hT
      rcases hcp with (⟨f, hf⟩ | ⟨u, hu⟩ | ⟨r, hr⟩ | ⟨p, hp⟩) | hp
      · rw [hf] at hT; cases hT
      · rw [hu] at hT; cases hT
      · rw [hr] at hT; cases hT
      · rw [hp] at hT; cases hT
      · subst hxo
        exact schedulingObjectRetirable_tcb (finalRetireAdmitted.schedulingRetirable hAdm
          ((schedulingKindAt_iff st _).mpr (by rw [hT]; trivial))) hT
  · exact .inr ⟨fun o hO s => (by rw [hU] at hO; cases hO; rfl),
      fun t hT => (by rw [hU] at hT; cases hT), .inr ⟨_, hU'⟩⟩

/-- **The retire makes no thread**: a thread after it was there before. -/
theorem retireFinalObject_tcb_back (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {oid : SeLe4n.ObjId} {t : TCB}
    (h : (retireFinalObject ec target recorder st).objects[oid]? = some (.tcb t)) :
    st.objects[oid]? = some (.tcb t) := by
  rcases retireFinalObject_key ec target recorder st hInv oid with e | ⟨-, -, hn | ⟨U, hU⟩⟩
  · rw [← e]; exact h
  · rw [hn] at h; cases h
  · rw [hU] at h; cases h

/-- **The retire keeps every thread but one it admits as detached**, key by
key: a thread stays, or the retire guard admitted it (`threadRetirable`) and it
is gone. -/
theorem retireFinalObject_tcb_cases (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {oid : SeLe4n.ObjId} {t : TCB}
    (h : st.objects[oid]? = some (.tcb t)) :
    (retireFinalObject ec target recorder st).objects[oid]? = some (.tcb t) ∨
      ((retireFinalObject ec target recorder st).objects[oid]? = none ∧
        threadRetirable st oid = true) := by
  rcases retireFinalObject_key ec target recorder st hInv oid with e | ⟨-, hR, hn | ⟨U, hU⟩⟩
  · rw [e]; exact .inl h
  · exact .inr ⟨hn, hR t h⟩
  · exfalso
    rcases (retireFinalObject_frame ec target recorder st hInv).2.2.2.2 oid with
      e | ⟨-, -, hn'⟩ | ⟨U', -, -, hU0, -⟩
    · rw [e, h] at hU; cases hU
    · rw [hn'] at hU; cases hU
    · rw [h] at hU0; cases hU0

/-- **The retire keeps a thread that holds a capability**: a thread with a
filled space slot is not quiescent, so the retire guard refuses it. -/
theorem retireFinalObject_getTcb?_of_slotCap (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {tid : SeLe4n.ThreadId} {t : TCB}
    (h : st.getTcb? tid = some t) {s : SeLe4n.Slot} (hs : (t.spaceSlotCap s).isSome = true) :
    (retireFinalObject ec target recorder st).getTcb? tid = some t := by
  have hPre := (SystemState.getTcb?_eq_some_iff st tid t).mp h
  refine (SystemState.getTcb?_eq_some_iff _ tid t).mpr ?_
  rcases retireFinalObject_tcb_cases ec target recorder st hInv hPre with e | ⟨-, hR⟩
  · exact e
  · obtain ⟨t', hT', -, -, hQ, -⟩ := threadRetirable_parts hR
    rw [hPre] at hT'; cases hT'
    have := threadQuiescent.slotCap hQ s
    simp only [KernelObject.slotCap] at this
    rw [this] at hs; cases hs

/-- **The retire keeps every thread the retire guard refuses.** -/
theorem retireFinalObject_tcb_kept (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {oid : SeLe4n.ObjId} {t : TCB}
    (h : st.objects[oid]? = some (.tcb t)) (hR : threadRetirable st oid = false) :
    (retireFinalObject ec target recorder st).objects[oid]? = some (.tcb t) := by
  rcases retireFinalObject_tcb_cases ec target recorder st hInv h with e | ⟨-, h'⟩
  · exact e
  · rw [hR] at h'; cases h'

/-- **The retire keeps every slot's capability**: a key it changes held none. -/
theorem retireFinalObject_slotCapAt (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) (r : SlotRef) :
    (retireFinalObject ec target recorder st).slotCapAt r = st.slotCapAt r := by
  rw [SystemState.slotCapAt_eq_bind, SystemState.slotCapAt_eq_bind]
  rcases retireFinalObject_key ec target recorder st hInv r.cnode with e | ⟨hb, -, ha⟩
  · rw [e]
  · have l : ((retireFinalObject ec target recorder st).objects[r.cnode]?).bind
        (fun o => o.slotCap r.slot) = none := by
      rcases ha with hn | ⟨U, hU⟩
      · rw [hn]; rfl
      · rw [hU]; rfl
    have r' : (st.objects[r.cnode]?).bind (fun o => o.slotCap r.slot) = none := by
      cases hs : st.objects[r.cnode]? with
      | none => rfl
      | some o => exact hb o hs r.slot
    rw [l, r']

/-- **The retire keeps every CNode slot lookup.** -/
theorem retireFinalObject_lookupSlotCap (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) (r : SlotRef) :
    SystemState.lookupSlotCap (retireFinalObject ec target recorder st) r =
      SystemState.lookupSlotCap st r := by
  rcases retireFinalObject_key ec target recorder st hInv r.cnode with e | ⟨hb, -, ha⟩
  · unfold SystemState.lookupSlotCap SystemState.lookupCNode; rw [e]
  · have hR : SystemState.lookupSlotCap st r = none := by
      unfold SystemState.lookupSlotCap SystemState.lookupCNode
      cases hs : st.objects[r.cnode]? with
      | none => rfl
      | some o =>
        cases o with
        | cnode cn => exact hb _ hs r.slot
        | _ => rfl
    rw [hR]
    unfold SystemState.lookupSlotCap SystemState.lookupCNode
    rcases ha with hn | ⟨U, hU⟩
    · rw [hn]
    · rw [hU]

/-- **The retire makes no untyped**: a key that held none holds none after. -/
theorem retireFinalObject_getUntyped?_none (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {u : SeLe4n.ObjId}
    (h : st.getUntyped? u = none) :
    (retireFinalObject ec target recorder st).getUntyped? u = none := by
  rw [SystemState.getUntyped?_eq_bind] at h ⊢
  rcases (retireFinalObject_frame ec target recorder st hInv).2.2.2.2 u with e | ⟨-, -, hn⟩ | ⟨U, -, -, hU, -⟩
  · rw [e]; exact h
  · rw [hn]; rfl
  · rw [hU] at h; simp [KernelObject.untyped?] at h

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

/-- **The recorded retire keeps the teardown's state well formed and only
shrinks roots**: the unrecord writes an untyped where an untyped stands, the
retire takes one carved object out
(`retireCarvedObject_preserves_teardownWellFormed`), and the ASID round writes
neither the objects nor the ASID table. -/
theorem retireRecordedObject_preserves_teardownWellFormed (ec : Concurrency.CoreId)
    (recorder : Nat) (x : SeLe4n.ObjId) (st : SystemState) (hW : teardownWellFormed st)
    (hSz : st.objects.size < st.objects.capacity) :
    teardownWellFormed (retireRecordedObject ec recorder x st) ∧
      vspaceRootsShrink st (retireRecordedObject ec recorder x st) := by
  unfold retireRecordedObject
  dsimp only
  have h1 : teardownWellFormed (retireUnrecord recorder x st) ∧
      vspaceRootsShrink st (retireUnrecord recorder x st) ∧
      (retireUnrecord recorder x st).objects.size < (retireUnrecord recorder x st).objects.capacity := by
    obtain ⟨hI, hZ, -, -, -, hK⟩ := retireUnrecord_frame recorder x st hW.1 hSz
    have hR : ∀ (oid : SeLe4n.ObjId) (r : VSpaceRoot),
        (retireUnrecord recorder x st).objects[oid]? =
          some (KernelObject.vspaceRoot r) ↔ st.objects[oid]? = some (KernelObject.vspaceRoot r) := by
      intro oid r
      rcases hK oid with e | ⟨U, U', hU, hU', -⟩
      · rw [e]
      · rw [hU, hU']; simp
    exact ⟨teardownWellFormed_of_roots_eq hI (retireUnrecord_asidTable _ _ _) hR hW,
      fun oid r' h' => ⟨r', (hR oid r').1 h', rfl, fun _ _ hm => hm, fun _ _ he => he,
        fun _ hs => hs⟩, hZ⟩
  generalize retireUnrecord recorder x st = st1 at h1
  obtain ⟨hW1, hS1', hRoom1⟩ := h1
  obtain ⟨hW2, hS2⟩ := retireCarvedObject_preserves_teardownWellFormed st1 x hW1 hRoom1
  split
  · refine ⟨teardownWellFormed_of_tables_eq
      ((asidReleaseRound_objects _ _ _))
      ((asidReleaseRound_asidTable _ _ _)) hW2, ?_⟩
    refine hS1'.trans (hS2.trans ?_)
    intro oid r' h'
    rw [asidReleaseRound_objects] at h'
    exact ⟨r', h', rfl, fun _ _ hm => hm, fun _ _ he => he, fun _ hs => hs⟩
  · refine ⟨teardownWellFormed_of_tables_eq rfl rfl hW2, hS1'.trans (hS2.trans ?_)⟩
    intro oid r' h'
    exact ⟨r', h', rfl, fun _ _ hm => hm, fun _ _ he => he, fun _ hs => hs⟩

/-- **The passive erase keeps the teardown's state well formed and keeps every
root**: a passive object is no root, and the ASID table is not written. -/
theorem eraseRetiredObject_preserves_teardownWellFormed (st : SystemState) (x : SeLe4n.ObjId)
    (hW : teardownWellFormed st) (hSz : st.objects.size < st.objects.capacity) :
    teardownWellFormed (eraseRetiredObject st x) ∧ vspaceRootsShrink st (eraseRetiredObject st x) := by
  obtain ⟨hI, -, -, -, -, hA, -, -⟩ := eraseRetiredObject_frame st x hW.1 hSz
  have hR : ∀ (oid : SeLe4n.ObjId) (r : VSpaceRoot),
      (eraseRetiredObject st x).objects[oid]? = some (KernelObject.vspaceRoot r) ↔
        st.objects[oid]? = some (KernelObject.vspaceRoot r) := by
    intro oid r
    rcases eraseRetiredObject_write st x hW.1 hSz oid with e | ⟨-, hp, hn⟩
    · rw [e]
    · rw [hn]
      constructor
      · intro h; cases h
      · intro h; rw [h] at hp; exact hp.elim
  exact ⟨teardownWellFormed_of_roots_eq hI hA hR hW,
    fun oid r' h' => ⟨r', (hR oid r').1 h', rfl, fun _ _ hm => hm, fun _ _ he => he,
      fun _ hs => hs⟩⟩

/-- **The retire keeps the teardown's state well formed and only shrinks
roots**: the passive erase keeps every root
(`eraseRetiredObject_preserves_teardownWellFormed`), and the recorded retire
takes one carved object out (`retireRecordedObject_preserves_teardownWellFormed`). -/
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
    split
    · obtain ⟨hW0, hS0⟩ := eraseRetiredObject_preserves_teardownWellFormed st _ hW hSz
      obtain ⟨-, room0, -⟩ := eraseRetiredObject_frame st (SeLe4n.ObjId.ofNat (target - 1)) hW.1 hSz
      obtain ⟨hW1, hS1⟩ := retireRecordedObject_preserves_teardownWellFormed ec recorder _ _ hW0 room0
      exact ⟨hW1, hS0.trans hS1⟩
    · exact ⟨hW, vspaceRootsShrink.refl st⟩
  · exact ⟨hW, vspaceRootsShrink.refl st⟩

/-- A retire of nothing is the identity. -/
theorem retireFinalObject_zero (ec : Concurrency.CoreId) (recorder : Nat) (st : SystemState) :
    retireFinalObject ec 0 recorder st = st := by
  unfold retireFinalObject; rfl

theorem eraseRetiredObject_fields (st : SystemState) (x : SeLe4n.ObjId) :
    (eraseRetiredObject st x).cdt = st.cdt ∧
    (eraseRetiredObject st x).scheduler = st.scheduler ∧
    (eraseRetiredObject st x).machine = st.machine := by
  rw [eraseRetiredObject_eq]; split <;> exact ⟨rfl, rfl, rfl⟩

theorem retireRecordedObject_fields (ec : Concurrency.CoreId) (recorder : Nat) (x : SeLe4n.ObjId)
    (st : SystemState) :
    (retireRecordedObject ec recorder x st).cdt = st.cdt ∧
    (retireRecordedObject ec recorder x st).scheduler = st.scheduler ∧
    (retireRecordedObject ec recorder x st).machine = st.machine := by
  unfold retireRecordedObject
  dsimp only
  have h1 := retireUnrecord_fields recorder x st
  generalize retireUnrecord recorder x st = st1 at h1
  obtain ⟨s2, m2, c2⟩ := retireCarvedObject_scheduler_machine_cdt st1 x
  split
  · rw [asidReleaseRound_cdt, asidReleaseRound_scheduler, asidReleaseRound_machine,
      c2, s2, m2]
    exact h1
  · rw [c2, s2, m2]
    exact h1

/-- **The retire writes no derivation edge, no scheduler and no machine
state.** -/
theorem retireFinalObject_fields (ec : Concurrency.CoreId) (target recorder : Nat) (st : SystemState) :
    (retireFinalObject ec target recorder st).cdt = st.cdt ∧
    (retireFinalObject ec target recorder st).scheduler = st.scheduler ∧
    (retireFinalObject ec target recorder st).machine = st.machine := by
  unfold retireFinalObject
  split
  · exact ⟨rfl, rfl, rfl⟩
  split
  · dsimp only
    split
    · obtain ⟨c0, s0, m0⟩ := eraseRetiredObject_fields st (SeLe4n.ObjId.ofNat (target - 1))
      obtain ⟨c1, s1, m1⟩ := retireRecordedObject_fields ec recorder (SeLe4n.ObjId.ofNat (target - 1))
        (eraseRetiredObject st (SeLe4n.ObjId.ofNat (target - 1)))
      exact ⟨c1.trans c0, s1.trans s0, m1.trans m0⟩
    · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

theorem storeUntypedWith_referenceTables (st : SystemState) (w : SeLe4n.ObjId)
    (f : UntypedObject → UntypedObject) :
    (st.storeUntypedWith w f).referenceTables = st.referenceTables := by
  cases hW : st.objects[w]? with
  | none => unfold SystemState.storeUntypedWith; rw [hW]
  | some o =>
    cases o with
    | untyped U =>
      exact storeObject_referenceTables (SystemState.storeObject_untyped_eq_storeUntypedWith hW f)
    | _ => unfold SystemState.storeUntypedWith; rw [hW]

theorem retireUnrecord_referenceTables (recorder : Nat) (x : SeLe4n.ObjId) (st : SystemState) :
    (retireUnrecord recorder x st).referenceTables = st.referenceTables := by
  have hR : ∀ kids st, (reparentChildren recorder kids st).referenceTables = st.referenceTables := by
    intro kids
    induction kids with
    | nil => intro st; rfl
    | cons c rest ih =>
      intro st
      simp only [reparentChildren]
      rw [ih, storeUntypedWith_referenceTables]
  unfold retireUnrecord adoptChildren
  dsimp only
  split
  · exact hR _ st
  · rw [storeUntypedWith_referenceTables, hR]

/-- **The retire writes no interrupt table, or writes nothing**: it erases
objects and rewrites untypeds' records. -/
theorem retireFinalObject_referenceTables (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) :
    retireFinalObject ec target recorder st = st ∨
    ((retireFinalObject ec target recorder st).irqHandlers = st.irqHandlers ∧
     target ≠ 0 ∧ st.objects.size < st.objects.capacity ∧
     finalRetireAdmitted st (SeLe4n.ObjId.ofNat (target - 1)) = true ∧
     retireFinalObject ec target recorder st =
       retireRecordedObject ec recorder (SeLe4n.ObjId.ofNat (target - 1))
         (eraseRetiredObject st (SeLe4n.ObjId.ofNat (target - 1)))) := by
  have hE : ∀ x, (eraseRetiredObject st x).referenceTables = st.referenceTables := fun x => by
    rw [eraseRetiredObject_eq]; split <;> rfl
  have hC : ∀ (s : SystemState) x, (retireCarvedObject s x).referenceTables = s.referenceTables :=
    fun s x => by unfold retireCarvedObject; split <;> rfl
  unfold retireFinalObject
  split
  · exact .inl rfl
  split
  · next hT hSz =>
    dsimp only
    split
    · next hAdm =>
      refine .inr ⟨?_, hT, hSz, hAdm, rfl⟩
      unfold retireRecordedObject
      dsimp only
      split
      · exact (hC _ _).trans ((retireUnrecord_referenceTables _ _ _).trans (hE _))
      · exact (hC _ _).trans ((retireUnrecord_referenceTables _ _ _).trans (hE _))
    · exact .inl rfl
  · exact .inl rfl

/-- **The retire keeps every interrupt back-link and service record**: the object
it erases holds neither — a carved kind, a thread or a scheduling context holds
none, and a passive object is retired only while its back-links are clear
(`passiveObjectRetirable`) — and an untyped it rewrites holds none. -/
theorem retireFinalObject_serviceIrqBackLinks (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) (oid : SeLe4n.ObjId) :
    ((objTableBackLinks (retireFinalObject ec target recorder st).objects[oid]?).1,
      (objTableBackLinks (retireFinalObject ec target recorder st).objects[oid]?).2.1) =
    ((objTableBackLinks st.objects[oid]?).1, (objTableBackLinks st.objects[oid]?).2.1) := by
  rcases retireFinalObject_admitted ec target recorder st with hEq | hAdm
  · rw [hEq]
  rcases (retireFinalObject_frame ec target recorder st hInv).2.2.2.2 oid with
    e | ⟨hxo, hcp, hn⟩ | ⟨U, U', -, hU, hU', -⟩
  · rw [e]
  · rw [hn]
    rcases hcp with hc | hE
    · rcases hc with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> (rw [h]; rfl)
    subst hxo
    by_cases hP : passiveKernelObject st.objects[SeLe4n.ObjId.ofNat (target - 1)]?
    · have hClear := (passiveObjectRetirable_parts (finalRetireAdmitted.retirable hAdm hP)).2
      rw [SystemState.tableBackLinksClear_iff] at hClear
      exact hClear.symm
    · revert hE hP
      cases st.objects[SeLe4n.ObjId.ofNat (target - 1)]? with
      | none => intro h; cases h
      | some o => cases o <;> intro _ hP <;> first | rfl | exact absurd trivial hP
  · rw [hU, hU']; rfl

/-- **An admitted retire leaves no thread or notification at its target**: one
there is an erasable kind (`erasableKindAt` reads the store), so the passive
erase takes it out, and nothing after writes a thread or a notification. -/
theorem retireFinalObject_target_taint_empty (ec : Concurrency.CoreId) (recorder : Nat)
    (x : SeLe4n.ObjId) (st : SystemState) (hInv : st.objects.invExt)
    (hSz : st.objects.size < st.objects.capacity) :
    objTaint (retireRecordedObject ec recorder x (eraseRetiredObject st x)).objects[x]? =
      DeclassificationTaint.empty := by
  obtain ⟨i0, room0, -⟩ := eraseRetiredObject_frame st x hInv hSz
  have hW := (retireRecordedObject_frame ec recorder x _ i0 room0).2.2.2.2 x
  have h0 : objTaint (eraseRetiredObject st x).objects[x]? = DeclassificationTaint.empty := by
    rw [eraseRetiredObject_eq]
    split
    · next hK =>
      have : (st.objects.erase x)[x]? = none := by
        simp only [RHTable_getElem?_eq_get?]
        exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_self st.objects x hInv
      simp only [this]; rfl
    · next hK =>
      have hNot : ¬ erasableKernelObject st.objects[x]? :=
        fun h => hK ((erasableKindAt_iff st x).mpr h)
      revert hNot
      cases st.objects[x]? with
      | none => intro _; rfl
      | some o => cases o <;> intro hNot <;> first | rfl | exact absurd trivial hNot
  rcases hW with e | ⟨-, -, hn⟩ | ⟨-, -, hne, -⟩
  · rw [e]; exact h0
  · rw [hn]; rfl
  · exact absurd rfl hne

/-- **The retire keeps the table references recorded**: it writes no interrupt
table and keeps every object's interrupt back-link and service record. -/
theorem retireFinalObject_preserves_tableReferencesRecorded (ec : Concurrency.CoreId)
    (target recorder : Nat) (st : SystemState) (hInv : st.objects.invExt)
    (hR : st.tableReferencesRecorded) :
    (retireFinalObject ec target recorder st).tableReferencesRecorded := by
  rcases retireFinalObject_referenceTables ec target recorder st with hEq | ⟨hI, -, -, -, -⟩
  · rw [hEq]; exact hR
  have hB := retireFinalObject_serviceIrqBackLinks ec target recorder st hInv
  refine ⟨fun irq n h => ?_, fun n h => ?_⟩
  · rw [hI] at h
    have := congrArg Prod.snd (hB n); simp only at this
    rw [this]; exact hR.irqHandlers irq n h
  · have := congrArg Prod.snd (hB n); simp only at this
    rw [this] at h; rw [hI]; exact hR.irqBound n h

/-- **The retire forgets its target's declassification provenance and keeps
every other object's**, or writes nothing: a thread or a notification at the
target is an erasable kind, so the passive erase takes its taint words out
(`retireFinalObject_target_taint_empty`), and the retire rewrites no other
thread's or notification's words.  So the id it frees carries no taint, and an
object a later carve puts there inherits none. -/
theorem retireFinalObject_taint_cleared (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) :
    retireFinalObject ec target recorder st = st ∨
      (retireFinalObject ec target recorder st).declassificationTaint =
        st.declassificationTaint.clearAt (SeLe4n.ObjId.ofNat (target - 1)) := by
  rcases retireFinalObject_referenceTables ec target recorder st with hEq | ⟨-, -, hSz, -, hSt⟩
  · exact .inl hEq
  refine .inr (funext fun k => ?_)
  by_cases hk : k = SeLe4n.ObjId.ofNat (target - 1)
  · subst hk
    rw [TaintMap.clearAt_self, SystemState.taintStored, hSt,
      retireFinalObject_target_taint_empty ec recorder _ st hInv hSz]
  · rw [TaintMap.clearAt_ne _ hk, SystemState.taintStored, SystemState.taintStored]
    rcases (retireFinalObject_frame ec target recorder st hInv).2.2.2.2 k with
      e | ⟨hxo, -, -⟩ | ⟨U, U', -, hU, hU', -⟩
    · rw [e]
    · exact absurd hxo hk
    · rw [hU, hU']; rfl

/-- **The retire writes no derivation edge.** -/
theorem retireFinalObject_cdt (ec : Concurrency.CoreId) (target recorder : Nat) (st : SystemState) :
    (retireFinalObject ec target recorder st).cdt = st.cdt :=
  (retireFinalObject_fields ec target recorder st).1

-- ============================================================================
-- §9  What the retire leaves of the keys a predicate admits
-- ============================================================================

theorem childListErase_of_not_records {l : List UntypedChild} {x : SeLe4n.ObjId}
    (h : childListRecords l x = false) : childListErase l x = l := by
  rw [childListErase_eq_filter, List.filter_eq_self]
  intro ch hm
  have hne : ch.objId ≠ x := fun e => by
    have hr := (childListRecords_iff l x).mpr ⟨ch, hm, e⟩
    rw [h] at hr; cases hr
  simpa using hne

/-- **The retire keeps every key a predicate admits**, when the predicate admits
neither the target, nor any untyped recording it, nor any child it records. -/
theorem retireFinalObject_objects_of_excluded (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) (p : SeLe4n.ObjId → Bool)
    (hx : target ≠ 0 → p (SeLe4n.ObjId.ofNat (target - 1)) = false)
    (hU : target ≠ 0 → ∀ w, untypedRecordsChild st w (SeLe4n.ObjId.ofNat (target - 1)) = true →
      p w = false)
    (hK : target ≠ 0 → ∀ y, untypedRecordsChild st (SeLe4n.ObjId.ofNat (target - 1)) y = true →
      p y = false)
    (o : SeLe4n.ObjId) (ho : p o = true) :
    (retireFinalObject ec target recorder st).objects[o]? = st.objects[o]? := by
  by_cases h0 : target = 0
  · rw [h0, retireFinalObject_zero]
  exact ((retireFinalObject_frame ec target recorder st hInv).2.2.2.2).objects_of_excluded p
    (hx h0) (hU h0) (hK h0) o ho

/-- **The retire records no child but those it adopts**: an untyped that records
`o` after it recorded `o` before, or recorded the target, which recorded `o`. -/
theorem retireFinalObject_untypedRecordsChild (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {w o : SeLe4n.ObjId}
    (h : untypedRecordsChild (retireFinalObject ec target recorder st) w o = true) :
    untypedRecordsChild st w o = true ∨
      (untypedRecordsChild st w (SeLe4n.ObjId.ofNat (target - 1)) = true ∧
        untypedRecordsChild st (SeLe4n.ObjId.ofNat (target - 1)) o = true) :=
  ((retireFinalObject_frame ec target recorder st hInv).2.2.2.2).recordsChild h

theorem filter_bne_filter {l : List SeLe4n.ObjId} {x : SeLe4n.ObjId} {p : SeLe4n.ObjId → Bool}
    (hx : p x = false) : (l.filter (· != x)).filter p = l.filter p := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    by_cases h : a = x
    · subst h; simp [List.filter_cons, hx, ih]
    · simp [List.filter_cons, h, ih]

/-- **The retire keeps the interrupt table, and the object index
on the keys a predicate admits**, when the predicate admits neither the target
nor the recorder. -/
theorem retireFinalObject_tables (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) (p : SeLe4n.ObjId → Bool)
    (hx : target ≠ 0 → p (SeLe4n.ObjId.ofNat (target - 1)) = false)
    (hR : recorder ≠ 0 → p (SeLe4n.ObjId.ofNat (recorder - 1)) = false)
    (hK : target ≠ 0 → ∀ y, untypedRecordsChild st (SeLe4n.ObjId.ofNat (target - 1)) y = true →
      p y = false) :
    (retireFinalObject ec target recorder st).irqHandlers = st.irqHandlers ∧
    (retireFinalObject ec target recorder st).objectIndex.filter p = st.objectIndex.filter p := by
  unfold retireFinalObject
  split
  · exact ⟨rfl, rfl⟩
  next h0 =>
  split
  · next hSz =>
    dsimp only
    split
    · have hS0 : ∀ y, untypedRecordsChild (eraseRetiredObject st (SeLe4n.ObjId.ofNat (target - 1)))
          (SeLe4n.ObjId.ofNat (target - 1)) y = untypedRecordsChild st (SeLe4n.ObjId.ofNat (target - 1)) y :=
        fun y => eraseRetiredObject_untypedRecordsChild st _ hInv hSz _ y
      have h1 : (eraseRetiredObject st (SeLe4n.ObjId.ofNat (target - 1))).irqHandlers = st.irqHandlers ∧
          (eraseRetiredObject st (SeLe4n.ObjId.ofNat (target - 1))).objectIndex.filter p =
            st.objectIndex.filter p := by
        rw [eraseRetiredObject_eq]
        split
        · exact ⟨rfl, filter_bne_filter (hx h0)⟩
        · exact ⟨rfl, rfl⟩
      generalize eraseRetiredObject st (SeLe4n.ObjId.ofNat (target - 1)) = s0 at h1 hS0 ⊢
      unfold retireRecordedObject
      dsimp only
      have hK0 : ∀ c ∈ retiredChildren s0 (SeLe4n.ObjId.ofNat (target - 1)), p c.objId = false := by
        intro c hc
        have := mem_retiredChildren hc
        rw [hS0] at this
        exact hK h0 _ this
      have h2 := retireUnrecord_tables recorder (SeLe4n.ObjId.ofNat (target - 1)) s0 p hR hK0
      rw [h1.1, h1.2] at h2
      generalize retireUnrecord recorder (SeLe4n.ObjId.ofNat (target - 1)) s0 = s1 at h2 ⊢
      have h3 : (retireCarvedObject s1 (SeLe4n.ObjId.ofNat (target - 1))).irqHandlers = st.irqHandlers ∧
          (retireCarvedObject s1 (SeLe4n.ObjId.ofNat (target - 1))).objectIndex.filter p =
            st.objectIndex.filter p := by
        unfold retireCarvedObject
        split
        · exact ⟨h2.1, (filter_bne_filter (hx h0)).trans h2.2⟩
        · exact h2
      split
      · exact h3
      · exact h3
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

-- ============================================================================
-- §10  What the retire keeps of the objects other objects name
-- ============================================================================

/-- **The retire keeps a busy passive object**: one whose own links are not
quiescent is not admitted. -/
theorem retireFinalObject_passive_kept (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {o : SeLe4n.ObjId}
    (hP : passiveKernelObject st.objects[o]?) (hKeep : passiveObjectQuiescent st o = false) :
    (retireFinalObject ec target recorder st).objects[o]? = st.objects[o]? := by
  rcases retireFinalObject_admitted ec target recorder st with hE | hAdm
  · rw [hE]
  rcases (retireFinalObject_frame ec target recorder st hInv).2.2.2.2 o with
    e | ⟨hxo, -, -⟩ | ⟨U, -, -, hU, -⟩
  · exact e
  · subst hxo
    have hR := passiveObjectRetirable_parts (finalRetireAdmitted.retirable hAdm hP)
    rw [hR.1] at hKeep; cases hKeep
  · rw [hU] at hP; simp only [passiveKernelObject] at hP

/-- **The retire keeps every key holding no carved, passive or untyped
object** — a thread or a scheduling context. -/
theorem retireFinalObject_kept_of_unretirable (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {o : SeLe4n.ObjId}
    (hC : ¬ carvedAt st o) (hP : ¬ erasableKernelObject st.objects[o]?)
    (hU : ∀ U, st.objects[o]? ≠ some (.untyped U)) :
    (retireFinalObject ec target recorder st).objects[o]? = st.objects[o]? := by
  rcases (retireFinalObject_frame ec target recorder st hInv).2.2.2.2 o with
    e | ⟨-, hcp, -⟩ | ⟨U, -, -, hU0, -⟩
  · exact e
  · rcases hcp with h | h
    · exact absurd h hC
    · exact absurd h hP
  · exact absurd hU0 (hU U)

/-- **The retire keeps every scheduling context but one it admits as
detached**: a context stays, or the retire guard admitted it
(`schedContextRetirable`) and it is gone. -/
theorem retireFinalObject_schedContext_cases (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {o : SeLe4n.ObjId} {sc : SchedContext}
    (h : st.objects[o]? = some (.schedContext sc)) :
    (retireFinalObject ec target recorder st).objects[o]? = some (.schedContext sc) ∨
      ((retireFinalObject ec target recorder st).objects[o]? = none ∧
        schedContextRetirable st o = true) := by
  rcases retireFinalObject_touched ec target recorder st hInv o with e | ⟨hT, -⟩ | ⟨hn, -, hR⟩
  · rw [e]; exact .inl h
  · rw [h] at hT; exact hT.elim
  · exact .inr ⟨hn, schedulingObjectRetirable_schedContext hR h⟩

/-- **The retire keeps every scheduling context the retire guard refuses.** -/
theorem retireFinalObject_schedContext (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {o : SeLe4n.ObjId} {sc : SchedContext}
    (h : st.objects[o]? = some (.schedContext sc)) (hR : schedContextRetirable st o = false) :
    (retireFinalObject ec target recorder st).objects[o]? = some (.schedContext sc) := by
  rcases retireFinalObject_schedContext_cases ec target recorder st hInv h with e | ⟨-, h'⟩
  · exact e
  · rw [hR] at h'; cases h'

/-- **What the retire leaves at a key that is not an untyped was there
before.** -/
theorem retireFinalObject_back (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {o : SeLe4n.ObjId} {obj : KernelObject}
    (h : (retireFinalObject ec target recorder st).objects[o]? = some obj)
    (hNU : ∀ U, obj ≠ .untyped U) :
    st.objects[o]? = some obj := by
  rcases retireFinalObject_key ec target recorder st hInv o with e | ⟨-, -, hn | ⟨U, hU⟩⟩
  · rw [← e]; exact h
  · rw [hn] at h; cases h
  · rw [hU] at h; cases h; exact absurd rfl (hNU U)

/-- WS-ZA ZA6.3: **the retire holds every release queue.**  It writes no
scheduler field, keeps every context the guard refuses, and erases only one the
guard admits — linked into no core's release queue (`schedContextRetirable`) —
so every key reads the same release link on every core. -/
theorem retireFinalObject_releaseStateAgree (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) :
    SystemState.releaseStateAgree (retireFinalObject ec target recorder st) st := by
  refine ⟨.of_objReleaseLinkOn fun k c => ?_,
    by rw [(retireFinalObject_fields ec target recorder st).2.1]⟩
  have hNoSc : (∀ sc, st.objects[k]? ≠ some (.schedContext sc)) →
      SystemState.objReleaseLinkOn (retireFinalObject ec target recorder st).objects[k]? c =
        SystemState.objReleaseLinkOn st.objects[k]? c := by
    intro hN
    have hPre : SystemState.objReleaseLinkOn st.objects[k]? c = none := by
      cases hP : st.objects[k]? with
      | none => rfl
      | some o => cases o <;> first | rfl | exact absurd hP (hN _)
    rw [hPre]
    cases hQ : (retireFinalObject ec target recorder st).objects[k]? with
    | none => rfl
    | some o =>
      cases o <;> first | rfl | skip
      rename_i sc
      exact absurd (retireFinalObject_back ec target recorder st hInv hQ
        (fun _ h => KernelObject.noConfusion h)) (hN sc)
  cases hP : st.objects[k]? with
  | none => rw [← hP]; exact hNoSc (fun _ h => by rw [hP] at h; cases h)
  | some o =>
    cases o with
    | schedContext sc =>
      rcases retireFinalObject_schedContext_cases ec target recorder st hInv hP with e | ⟨e, hR⟩
      · rw [e]
      · obtain ⟨sc', hS', -, -, -, h0, -⟩ := schedContextRetirable_parts hR
        rw [hP] at hS'; cases hS'
        rw [e]
        simp [SystemState.objReleaseLinkOn, SchedContext.releaseLinkOn, h0]
    | _ => rw [← hP]; exact hNoSc (fun _ h => by rw [hP] at h; cases h)

/-- An object a retire may touch holds no yield link end. -/
theorem objYieldCodes_of_retireTouched {o : Option KernelObject} (h : retireTouched o) :
    objYieldCodes o = (0, 0) := by
  cases o with
  | none => rfl
  | some obj => cases obj <;> first | rfl | exact h.elim

/-- WS-ZA ZA6.6: **the retire keeps every yield code.**  It erases a thread or
a context only when the guard admits it, and the guard admits neither with a
yield link end (`threadLinksQuiescent`, `schedContextRetirable`), so every key
reads the codes it read. -/
theorem retireFinalObject_yieldLinksKept (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) :
    YieldLinksKept (retireFinalObject ec target recorder st) st := fun k => by
  rcases retireFinalObject_touched ec target recorder st hInv k with e | ⟨t1, t2⟩ | ⟨hn, -, hR⟩
  · rw [e]
  · rw [objYieldCodes_of_retireTouched t1, objYieldCodes_of_retireTouched t2]
  · rw [hn]
    cases hP : st.objects[k]? with
    | none => rfl
    | some o =>
      cases o with
      | tcb t =>
        obtain ⟨t', hT', -, -, hQ, -⟩ :=
          threadRetirable_parts (schedulingObjectRetirable_tcb hR hP)
        rw [hP] at hT'; cases hT'
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h0, -⟩ :=
          threadQuiescent_codes hQ
        simp [objYieldCodes, h0]
      | schedContext sc =>
        obtain ⟨sc', hS', -, -, -, -, h0⟩ :=
          schedContextRetirable_parts (schedulingObjectRetirable_schedContext hR hP)
        rw [hP] at hS'; cases hS'
        simp [objYieldCodes, h0]
      | _ => rfl

/-- A reply linked upward is not quiescent. -/
theorem passiveObjectQuiescent_of_next {st : SystemState} {o : SeLe4n.ObjId} {r : Reply}
    (hR : st.objects[o]? = some (.reply r)) (hN : r.next.isSome = true) :
    passiveObjectQuiescent st o = false := by
  cases hn : r.next with
  | none => rw [hn] at hN; cases hN
  | some _ => simp [passiveObjectQuiescent, SystemState.getObject?, hR, hn]

/-- A reply linked downward is not quiescent. -/
theorem passiveObjectQuiescent_of_prev {st : SystemState} {o : SeLe4n.ObjId} {r : Reply}
    (hR : st.objects[o]? = some (.reply r)) (hP : r.prev.isSome = true) :
    passiveObjectQuiescent st o = false := by
  cases hp : r.prev with
  | none => rw [hp] at hP; cases hP
  | some _ => simp [passiveObjectQuiescent, SystemState.getObject?, hR, hp]

/-- A quiescent object is a passive one. -/
theorem passiveObjectQuiescent.passive {st : SystemState} {x : SeLe4n.ObjId}
    (h : passiveObjectQuiescent st x = true) : passiveKernelObject st.objects[x]? := by
  unfold passiveObjectQuiescent at h
  rw [SystemState.getObject?_eq_getElem] at h
  cases hO : st.objects[x]? with
  | none => rw [hO] at h; cases h
  | some o => rw [hO] at h; cases o <;> first | trivial | cases h

/-- A scheduling context heading a reply stack is not retired. -/
theorem schedContextRetirable_false_of_scReply {st : SystemState} {x : SeLe4n.ObjId}
    {sc : SchedContext} (hS : st.objects[x]? = some (.schedContext sc)) {r : SeLe4n.ReplyId}
    (hR : sc.scReply = some r) : schedContextRetirable st x = false := by
  simp [schedContextRetirable, SystemState.getObject?, hS, hR]

-- ============================================================================
-- §  What the retire of a thread or a scheduling context leaves
-- ============================================================================

/-- **A thread after the retire is the thread before it**, at its key. -/
theorem retireFinalObject_tcb_post (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {oid : SeLe4n.ObjId} {t : TCB}
    (h : (retireFinalObject ec target recorder st).objects[oid]? = some (.tcb t)) :
    (retireFinalObject ec target recorder st).objects[oid]? = st.objects[oid]? := by
  rw [h, retireFinalObject_tcb_back ec target recorder st hInv h]

/-- **The retire keeps every thread but a quiescent one it erases**: a thread
stays, or it is gone and it was stored under its own id, quiescent, held by no
core and no idle thread. -/
theorem retireFinalObject_tcb_kept_or_quiescent (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {oid : SeLe4n.ObjId} {t : TCB}
    (h : st.objects[oid]? = some (.tcb t)) :
    (retireFinalObject ec target recorder st).objects[oid]? = st.objects[oid]? ∨
      ((retireFinalObject ec target recorder st).objects[oid]? = none ∧
        t.tid.val = oid.val ∧ isIdleThreadId t.tid = false ∧ threadQuiescent t = true ∧
        threadHeldOnSomeCore st t.tid = false) := by
  rcases retireFinalObject_tcb_cases ec target recorder st hInv h with e | ⟨hn, hR⟩
  · rw [e, h]; exact .inl rfl
  · obtain ⟨t', hT', hId, hIdle, hQ, hH⟩ := threadRetirable_parts hR
    rw [h] at hT'; cases hT'
    exact .inr ⟨hn, hId, hIdle, hQ, hH⟩

/-- A quiescent thread waits on no server. -/
theorem threadQuiescent_blockingServer {t : TCB} (h : threadQuiescent t = true) :
    t.blockingServer? = none := by
  simp only [TCB.blockingServer?, threadQuiescent_ipcState h]

/-- A quiescent thread links into no core's run queue. -/
theorem threadQuiescent_runLinkOn {t : TCB} (h : threadQuiescent t = true) (c : Concurrency.CoreId) :
    t.runCoreCode ≠ c.val + 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h0, -⟩ := threadQuiescent_codes h
  omega

/-- **The retire keeps every run-queue link**: a thread it keeps keeps its
links, and the thread it erases was on no core's queue. -/
theorem retireFinalObject_runLinkOn (ec : Concurrency.CoreId) (target recorder : Nat)
    {st : SystemState} (hObjInv : st.objects.invExt) (c : Concurrency.CoreId)
    (t : SeLe4n.ThreadId) :
    (retireFinalObject ec target recorder st).runLinkOn c t = st.runLinkOn c t := by
  unfold SystemState.runLinkOn SystemState.getTcb?
  cases hk : st.objects[t.toObjId]? with
  | none =>
    cases hp : (retireFinalObject ec target recorder st).objects[t.toObjId]? with
    | none => rfl
    | some o =>
      cases o with
      | tcb x => rw [retireFinalObject_tcb_back ec target recorder st hObjInv hp] at hk; cases hk
      | _ => rfl
  | some o =>
    cases o with
    | tcb x =>
      rcases retireFinalObject_tcb_kept_or_quiescent ec target recorder st hObjInv hk with
        e | ⟨hn, -, -, hQ, -⟩
      · rw [e, hk]
      · rw [hn]
        simp only [TCB.runLinkOn, if_neg (threadQuiescent_runLinkOn hQ c)]
    | _ =>
      cases hp : (retireFinalObject ec target recorder st).objects[t.toObjId]? with
      | none => rfl
      | some o' =>
        cases o' with
        | tcb x => rw [retireFinalObject_tcb_back ec target recorder st hObjInv hp] at hk; cases hk
        | _ => rfl

/-- **The retire keeps the state fields monotone**: every thread but the one it
erases is kept, and that one was suspended, so it was neither runnable nor
active. -/
theorem retireFinalObject_stateMono (ec : Concurrency.CoreId) (target recorder : Nat)
    {st : SystemState} (hObjInv : st.objects.invExt) :
    SystemState.StateMono st (retireFinalObject ec target recorder st) := by
  refine SystemState.StateMono.of_pointwise_erase (fun t x hx => ?_) (fun t x' hx' hc => ?_)
    (fun t x' hx' hn => ?_)
  · have hk := (SystemState.getTcb?_eq_some_iff st t x).mp hx
    rcases retireFinalObject_tcb_kept_or_quiescent ec target recorder st hObjInv hk with
      e | ⟨hn, -, -, hQ, -⟩
    · exact .inl ⟨x, (SystemState.getTcb?_eq_some_iff _ t x).mpr (e.trans hk), ⟨id, id, rfl⟩⟩
    · refine .inr ⟨?_, fun hA => hA (threadQuiescent_codes hQ).1⟩
      unfold SystemState.getTcb?; rw [hn]
  · have hp := (SystemState.getTcb?_eq_some_iff _ t x').mp hx'
    exact hc x' ((SystemState.getTcb?_eq_some_iff st t x').mpr
      (retireFinalObject_tcb_back ec target recorder st hObjInv hp))
  · have hp := (SystemState.getTcb?_eq_some_iff _ t x').mp hx'
    rw [(SystemState.getTcb?_eq_some_iff st t x').mpr
      (retireFinalObject_tcb_back ec target recorder st hObjInv hp)] at hn
    cases hn

-- ============================================================================
-- §8  A store scan bounds a sweep
-- ============================================================================

/-- A conjunction folded from `false` stays `false`. -/
private theorem slots_foldl_and_false {α β : Type} (p : α → β → Bool)
    (l : List (Option (RobinHood.RHEntry α β))) :
    l.foldl (fun acc slot => match slot with
      | none => acc | some e => acc && p e.key e.value) false = false := by
  induction l with
  | nil => rfl
  | cons hd tl ih => cases hd <;> simpa using ih

private theorem slots_foldl_preserves_of_and {α β γ : Type} (p : α → β → Bool)
    (f : γ → α → β → γ) (P : γ → Prop)
    (hStep : ∀ acc k v, p k v = true → P acc → P (f acc k v)) :
    ∀ (l : List (Option (RobinHood.RHEntry α β))) (b : Bool) (init : γ),
      l.foldl (fun acc slot => match slot with
        | none => acc | some e => acc && p e.key e.value) b = true → P init →
      P (l.foldl (fun acc slot => match slot with
        | none => acc | some e => f acc e.key e.value) init) := by
  intro l
  induction l with
  | nil => intro _ _ _ h; exact h
  | cons hd tl ih =>
    intro b init hFold hInit
    cases hd with
    | none => exact ih b init hFold hInit
    | some e =>
      simp only [List.foldl_cons] at hFold ⊢
      have hb : (b && p e.key e.value) = true := by
        cases h : (b && p e.key e.value)
        · rw [h, slots_foldl_and_false] at hFold; cases hFold
        · rfl
      exact ih _ _ hFold (hStep init e.key e.value (Bool.and_eq_true _ _ |>.mp hb).2 hInit)

/-- **A sweep over a table that a passing scan bounds**: a property the sweep's
body keeps at every entry the scan accepts holds after the sweep.  The scan and
the sweep visit the same slots, so this needs no `invExt` — what lets a
runtime check over the store prove that a sweep over the same store has
nothing to do. -/
theorem RobinHood.RHTable.fold_preserves_of_fold_and {α β γ : Type} [BEq α] [Hashable α]
    [LawfulBEq α] (t : RobinHood.RHTable α β) (p : α → β → Bool)
    (hFold : t.fold true (fun acc k v => acc && p k v) = true)
    (init : γ) (f : γ → α → β → γ) (P : γ → Prop) (hInit : P init)
    (hStep : ∀ acc k v, p k v = true → P acc → P (f acc k v)) :
    P (t.fold init f) := by
  rw [RobinHood.RHTable.fold_eq_slots_foldl] at hFold ⊢
  rw [← Array.foldl_toList] at hFold ⊢
  exact slots_foldl_preserves_of_and p f P hStep _ true init hFold hInit
