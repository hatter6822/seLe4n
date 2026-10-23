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
# Retiring an object with its final capability

WS-ZA ZA5.4 part 21 (plan D2).  seL4's `cteDelete` runs `finaliseCap` on a
capability when `isFinalCapability` holds, and the object goes with its last
capability.  For the four memory kinds a carve makes — a frame, a page table,
an address-space root and an untyped — the finalisation is the unmap and
detach the teardown already does (`finaliseDestroyedCapabilities`); this module
is what follows it: the object leaves the store (`retireCarvedObject`, the
store's one erase, which the untyped reset uses too).

**The passive kernel kinds** (part 22, `v0.36.133`).  An endpoint, a
notification, a reply or a CNode goes the same way when seL4's `finaliseCap`
would have nothing to cancel (`passiveObjectQuiescent`) and nothing names it
outside a slot (`passiveObjectRetirable`: no object by id, no service
registration or graph entry, no interrupt handler); it leaves the store first
(`retirePassiveObject`), then its recorder's list.  One that fails either check
outlives its last capability, recorded, until the finalise of its kind lands
(`docs/planning/UNTYPED_RESET_PLAN.md` rows 23, 25 and 26).

**What is decided before the slot is emptied** (`slotRetireTarget`): the
capability names the object (`Capability.namedObject`), the capability is final
(`SystemState.capIsFinal`, read from the slot's four link words), and the
object is retirable (`retirableKind`): a frame, a page table, a root, an
untyped that records no child, or a passive kernel kind.  Under the capability bundle a final capability
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
object kind is finalised and retired with its last capability (parts 22–26), a
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
page table, an address-space root, an untyped whose child list records
nothing (see the module docstring for why an untyped with a live record
stays), or one of the four passive kernel kinds (an endpoint, a notification,
a reply or a CNode), which the retire takes out only while it is quiescent and
unreferenced (`passiveObjectRetirable`). -/
@[inline] def retirableKind (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  match st.getObjectType? x with
  | some .frame | some .pageTable | some .vspaceRoot => true
  | some .endpoint | some .notification | some .reply | some .cnode => true
  | some .untyped =>
    match st.getUntyped? x with
    | some U => U.children.isEmpty
    | none => false
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

theorem slotRetireTarget_of_empty {st : SystemState} {cnode : SeLe4n.ObjId}
    {slot : SeLe4n.Slot} (h : st.slotCapAt ⟨cnode, slot⟩ = none) :
    slotRetireTarget st cnode slot = 0 := by
  unfold slotRetireTarget; rw [h]

-- ============================================================================
-- §3a  The passive kernel kinds
-- ============================================================================

/-- **Whether an IPC state, held as its two codes, names the object `x`**: a
thread blocked on `x` as an endpoint (sending, receiving, calling or awaiting
a reply through it) or as a notification.  On the codes, so no state is
built (`ThreadIpcState.ofCodes`: state `0` is a send at object `o + 1`, every
other state is on the object word itself). -/
@[inline] def ipcCodesName (objCode stateCode : Nat) (x : SeLe4n.ObjId) : Bool :=
  if stateCode = 0 then objCode == x.val + 1 else objCode == x.val

/-- **Whether an object names `x` by its id outside a slot**: a thread blocked
on it (`ipcCodesName`), bound to it as its notification, or linked to it as
its reply (a caller's reply, a receiver's stashed reply); another reply's
stack link to it; a scheduling context whose reply stack it heads.  These are
every reference by id an endpoint, a notification, a reply or a CNode can have
in an object; a capability naming it lies in a slot, which finality reads. -/
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

/-- **No object names `x` by id**: the object table walked once, in place. -/
@[inline] def storeNamesNone (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  st.objects.fold true fun acc _ o => acc && !objectNamesById o x

/-- **No service registration holds a capability naming `x`**: a registration
keeps its endpoint's capability outside every slot, so the finality the tree
answers does not see it, and it counts as a capability here. -/
@[inline] def registryNamesNone (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  st.serviceRegistry.fold true fun acc _ reg =>
    acc && (match reg.endpointCap.namedObject with | some e => e != x | none => true)

/-- **No service-graph entry is backed by or owned by `x`.** -/
@[inline] def servicesNameNone (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  st.services.fold true fun acc _ e =>
    acc && e.identity.backingObject != x && e.identity.owner != x

/-- **No interrupt is handled through `x`**: the handler table names its
notification by id, where seL4 keeps a capability in the interrupt's slot. -/
@[inline] def irqHandlersNameNone (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  st.irqHandlers.fold true fun acc _ n => acc && n != x

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
with no caller and no stack link (`reply_remove` does nothing); a CNode whose
every slot is empty (the zombie loop deletes nothing). -/
@[inline] def passiveObjectQuiescent (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  match st.getObject? x with
  | some (.endpoint ep) => ep.sendHeadCode == 0 && ep.recvHeadCode == 0
  | some (.notification n) => n.waitHeadCode == 0 && n.boundTCBCode == 0
  | some (.reply r) => r.callerCode == 0 && r.prev.isNone && r.next.isNone
  | some (.cnode cn) => cn.cells.all (·.isNone)
  | _ => false

/-- **Whether a final delete retires the passive object at `x`**: it is
quiescent, and nothing names it by id: no object (`storeNamesNone`), no
service registration or service-graph entry, no interrupt handler.  A passive
object that fails this outlives its last capability, as every kernel object did
before `v0.36.133`; the cancelling finalisation that would retire it is
`docs/planning/UNTYPED_RESET_PLAN.md` rows 23, 25 and 26. -/
@[inline] def passiveObjectRetirable (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  passiveObjectQuiescent st x && storeNamesNone st x && registryNamesNone st x &&
    servicesNameNone st x && irqHandlersNameNone st x

/-- **Whether a final delete retires its target `x` at all**: anything but a
passive object is retired as part 21 retires it, and a passive object only
while `passiveObjectRetirable` holds. -/
@[inline] def finalRetireAdmitted (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  !passiveKindAt st x || passiveObjectRetirable st x

/-- **Erase a passive object** — an endpoint, a notification, a reply or a CNode
— from the object store, with its index row, its index-set entry and its type,
as `retireCarvedObject` erases a carved memory object; the identity at any
other key.  `retireFinalObject` runs it only on an object
`passiveObjectRetirable` admits. -/
def retirePassiveObject (st : SystemState) (x : SeLe4n.ObjId) : SystemState :=
  if passiveKindAt st x then
    { st with
        objects := st.objects.erase x
        objectIndex := st.objectIndex.filter (· != x)
        objectIndexSet := st.objectIndexSet.erase x
        lifecycle := { objectTypes := st.lifecycle.objectTypes.erase x } }
  else st

/-- `retirePassiveObject` as compiled: each table erased out of line over the
state it is handed, as `retireCarvedObjectImpl` does. -/
def retirePassiveObjectImpl (st : SystemState) (x : SeLe4n.ObjId) : SystemState :=
  if passiveKindAt st x then
    withObjectTypeErased (withObjectIndexSetErased (withObjectUnindexed (withObjectErased st x) x) x) x
  else st

@[csimp] theorem retirePassiveObject_eq_impl : @retirePassiveObject = @retirePassiveObjectImpl := by
  funext st x
  unfold retirePassiveObject retirePassiveObjectImpl withObjectTypeErased withObjectIndexSetErased
    withObjectUnindexed withObjectErased
  split
  · rw [objIdListDrop_eq_filter]; simp
  · rfl

/-- **`x` taken out of the child list of the untyped at `w`**, written in its
slot. -/
@[inline] def unrecordChild (st : SystemState) (w x : SeLe4n.ObjId) : SystemState :=
  st.storeUntypedWith w fun U => { U with children := childListErase U.children x }

/-- **The retire after the passive erase**: `x` leaves the child list of its
recorder (`recorder`, a word as `slotRetireRecorder` reads it), a carved `x`
leaves the store, and a root's ASID gets its acknowledged round. -/
def retireRecordedObject (executingCore : Concurrency.CoreId) (recorder : Nat) (x : SeLe4n.ObjId)
    (st : SystemState) : SystemState :=
  let st1 := if recorder = 0 then st else unrecordChild st (SeLe4n.ObjId.ofNat (recorder - 1)) x
  match st1.getVSpaceRoot? x with
  | some root => retypeAsidRoundStep executingCore root.asid (retireCarvedObject st1 x)
  | none => retireCarvedObject st1 x

/-- **Retire what a final delete destroyed** (`target`, `recorder`: the words
`slotRetireTarget` and `slotRetireRecorder` read before the slot was emptied):
a passive kernel kind leaves the store (`retirePassiveObject`, the identity on
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
      retireRecordedObject executingCore recorder x (retirePassiveObject st x)
    else st
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

/-- A passive object is not carved. -/
theorem not_carvedAt_of_passive {st : SystemState} {x : SeLe4n.ObjId}
    (h : passiveKernelObject st.objects[x]?) : ¬ carvedAt st x := by
  rintro (⟨f, hf⟩ | ⟨u, hu⟩ | ⟨r, hr⟩ | ⟨p, hp⟩)
  · rw [hf] at h; exact h
  · rw [hu] at h; exact h
  · rw [hr] at h; exact h
  · rw [hp] at h; exact h

theorem retirePassiveObject_of_not (st : SystemState) (x : SeLe4n.ObjId)
    (h : ¬ passiveKernelObject st.objects[x]?) : retirePassiveObject st x = st := by
  unfold retirePassiveObject
  rw [if_neg (fun h' => h ((passiveKindAt_iff st x).mp h'))]

/-- **The passive erase's frame**: the table keeps its invariant and headroom;
the scheduler, the machine, the tree and the ASID table are unchanged; every
key but `x` holds what it held, and `x` too unless it held a passive object,
which is now absent. -/
theorem retirePassiveObject_frame (st : SystemState) (x : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hSz : st.objects.size < st.objects.capacity) :
    (retirePassiveObject st x).objects.invExt ∧
    (retirePassiveObject st x).objects.size < (retirePassiveObject st x).objects.capacity ∧
    (retirePassiveObject st x).scheduler = st.scheduler ∧
    (retirePassiveObject st x).machine = st.machine ∧
    (retirePassiveObject st x).cdt = st.cdt ∧
    (retirePassiveObject st x).asidTable = st.asidTable ∧
    (∀ oid : SeLe4n.ObjId, oid ≠ x → (retirePassiveObject st x).objects[oid]? = st.objects[oid]?) ∧
    ((retirePassiveObject st x).objects[x]? = st.objects[x]? ∨
      (passiveKernelObject st.objects[x]? ∧ (retirePassiveObject st x).objects[x]? = none)) := by
  by_cases hP : passiveKernelObject st.objects[x]?
  · have hE : retirePassiveObject st x =
        { st with
          objects := st.objects.erase x
          objectIndex := st.objectIndex.filter (· != x)
          objectIndexSet := st.objectIndexSet.erase x
          lifecycle := { objectTypes := st.lifecycle.objectTypes.erase x } } := by
      unfold retirePassiveObject; rw [if_pos ((passiveKindAt_iff st x).mpr hP)]
    rw [hE]
    refine ⟨SeLe4n.Kernel.RobinHood.RHTable.erase_preserves_invExt st.objects x hInv hSz,
      SeLe4n.Kernel.RobinHood.RHTable.erase_size_lt_capacity st.objects x hSz, rfl, rfl, rfl, rfl,
      fun oid hK => ?_,
      .inr ⟨hP, SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_self st.objects x hInv⟩⟩
    have hNe : ¬(x == oid) = true := by intro h; exact hK (eq_of_beq h).symm
    exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_ne st.objects x oid hNe hInv hSz
  · rw [retirePassiveObject_of_not st x hP]
    exact ⟨hInv, hSz, rfl, rfl, rfl, rfl, fun _ _ => rfl, .inl rfl⟩

/-- **A final-delete retire write** of `x`: every key holds what it held, but
`x`, a carved or passive object now absent, and untypeds that lost their
records of `x`. -/
def finalRetireWrite (st st' : SystemState) (x : SeLe4n.ObjId) : Prop :=
  ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
    (oid = x ∧ (carvedAt st oid ∨ passiveKernelObject st.objects[oid]?) ∧
      st'.objects[oid]? = none) ∨
    ∃ U, st.objects[oid]? = some (KernelObject.untyped U) ∧
      st'.objects[oid]? = some (KernelObject.untyped (untypedWithoutChild U x))

/-- **The passive erase as a write**: every key holds what it held, but `x`,
a passive object now absent. -/
theorem retirePassiveObject_write (st : SystemState) (x : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hSz : st.objects.size < st.objects.capacity) (oid : SeLe4n.ObjId) :
    (retirePassiveObject st x).objects[oid]? = st.objects[oid]? ∨
      (oid = x ∧ passiveKernelObject st.objects[oid]? ∧ (retirePassiveObject st x).objects[oid]? = none) := by
  obtain ⟨-, -, -, -, -, -, hNe, hAt⟩ := retirePassiveObject_frame st x hInv hSz
  by_cases hK : oid = x
  · subst hK
    rcases hAt with e | ⟨hp, hn⟩
    · exact .inl e
    · exact .inr ⟨rfl, hp, hn⟩
  · exact .inl (hNe oid hK)

/-- **A passive erase followed by a retire write is a retire write.** -/
theorem finalRetireWrite.of_passive {st st0 st' : SystemState} {x : SeLe4n.ObjId}
    (h0 : ∀ oid : SeLe4n.ObjId, st0.objects[oid]? = st.objects[oid]? ∨
      (oid = x ∧ passiveKernelObject st.objects[oid]? ∧ st0.objects[oid]? = none))
    (h : finalRetireWrite st0 st' x) : finalRetireWrite st st' x := by
  intro oid
  rcases h oid with e | ⟨hx, hcp, hn⟩ | ⟨U, hU, hU'⟩
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
  · rcases h0 oid with e0 | ⟨-, -, hn0⟩
    · exact .inr (.inr ⟨U, e0 ▸ hU, hU'⟩)
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
      · refine .inr (.inl ⟨rfl, .inl ?_, hn⟩)
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
    · obtain ⟨i0, room0, s0, m0, c0, -, -, -⟩ := retirePassiveObject_frame st _ hInv hSz
      obtain ⟨i, s, m, c, w⟩ := retireRecordedObject_frame ec recorder _ _ i0 room0
      exact ⟨i, s.trans s0, m.trans m0, c.trans c0,
        finalRetireWrite.of_passive (retirePassiveObject_write st _ hInv hSz) w⟩
    · exact ⟨hInv, rfl, rfl, rfl, fun _ => .inl rfl⟩
  · exact ⟨hInv, rfl, rfl, rfl, fun _ => .inl rfl⟩

/-- **The object kinds a final-delete retire can touch**: what a reset touches
(`resetTouched`) and the four passive kinds.  None is a TCB or a scheduling
context, so none feeds the scheduler. -/
def retireTouched : Option KernelObject → Prop
  | some (.tcb _) => False
  | some (.schedContext _) => False
  | _ => True

theorem resetTouched.retireTouched {o : Option KernelObject} (h : resetTouched o) : retireTouched o := by
  cases o with
  | none => trivial
  | some obj => cases obj <;> first | trivial | exact absurd h (by simp [resetTouched])

/-- A reset-touched write is a retire-touched write. -/
theorem resetTouchedWrite.retireTouched {st st' : SystemState}
    (h : ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
      (resetTouched st.objects[oid]? ∧ resetTouched st'.objects[oid]?)) (oid : SeLe4n.ObjId) :
    st'.objects[oid]? = st.objects[oid]? ∨
      (retireTouched st.objects[oid]? ∧ retireTouched st'.objects[oid]?) := by
  rcases h oid with e | ⟨a, b⟩
  · exact .inl e
  · exact .inr ⟨a.retireTouched, b.retireTouched⟩

/-- **The retire touches only what a retire may touch**: every key holds what
it held, or a kind `retireTouched` admits on both sides. -/
theorem finalRetireWrite.touched {st st' : SystemState} {x : SeLe4n.ObjId}
    (h : finalRetireWrite st st' x) (oid : SeLe4n.ObjId) :
    st'.objects[oid]? = st.objects[oid]? ∨
      (retireTouched st.objects[oid]? ∧ retireTouched st'.objects[oid]?) := by
  rcases h oid with e | ⟨-, hcp, hn⟩ | ⟨U, hU, hU'⟩
  · exact .inl e
  · refine .inr ⟨?_, by rw [hn]; trivial⟩
    rcases hcp with (⟨f, hf⟩ | ⟨u, hu⟩ | ⟨r, hr⟩ | ⟨p, hp⟩) | hp
    · rw [hf]; trivial
    · rw [hu]; trivial
    · rw [hr]; trivial
    · rw [hp]; trivial
    · revert hp
      cases st.objects[oid]? with
      | none => intro _; trivial
      | some o => cases o <;> first | (intro _; trivial) | (intro h; simp [passiveKernelObject] at h)
  · rw [hU, hU']; exact .inr ⟨trivial, trivial⟩

/-- **The passive erase moves no record**: it erases no untyped. -/
theorem retirePassiveObject_untypedRecordsChild (st : SystemState) (x : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hSz : st.objects.size < st.objects.capacity) (w y : SeLe4n.ObjId) :
    untypedRecordsChild (retirePassiveObject st x) w y = untypedRecordsChild st w y := by
  unfold untypedRecordsChild SystemState.getUntyped?
  rcases retirePassiveObject_write st x hInv hSz w with e | ⟨-, hp, hn⟩
  · rw [e]
  · rw [hn]; revert hp
    cases st.objects[w]? with
    | none => intro _; rfl
    | some o => cases o <;> first | (intro _; rfl) | (intro h; simp [passiveKernelObject] at h)

/-- **After the recorded retire no untyped records `x`**, when the recorder
word answers truly and at most one untyped recorded `x`. -/
theorem retireRecordedObject_unrecorded (ec : Concurrency.CoreId) (recorder : Nat) (x : SeLe4n.ObjId)
    (st : SystemState) (hInv : st.objects.invExt) (hSz : st.objects.size < st.objects.capacity)
    (hR1 : recorder ≠ 0 → untypedRecordsChild st (SeLe4n.ObjId.ofNat (recorder - 1)) x = true)
    (hR0 : recorder = 0 → ∀ w, untypedRecordsChild st w x = false)
    (hUniq : ∀ u v, untypedRecordsChild st u x = true → untypedRecordsChild st v x = true → u = v) :
    ∀ (u : SeLe4n.ObjId) (U' : UntypedObject),
      (retireRecordedObject ec recorder x st).objects[u]? = some (KernelObject.untyped U') →
      ∀ ch ∈ U'.children, ch.objId ≠ x := by
  unfold retireRecordedObject
  dsimp only
  -- what the unrecord leaves: no untyped recording `x`
  have h1 : ∀ (u : SeLe4n.ObjId) (U' : UntypedObject),
      (if recorder = 0 then st else unrecordChild st (SeLe4n.ObjId.ofNat (recorder - 1)) x).objects[u]? =
        some (KernelObject.untyped U') → ∀ ch ∈ U'.children, ch.objId ≠ x := by
    intro u U' hu ch hch hc
    split at hu
    · next h0 =>
      have := hR0 h0 u
      unfold untypedRecordsChild SystemState.getUntyped? at this
      rw [hu] at this
      exact absurd ((childListRecords_iff _ _).mpr ⟨ch, hch, hc⟩) (by simp [this])
    · next h0 =>
      have hw := hR1 h0
      rcases unrecordChild_cases st (SeLe4n.ObjId.ofNat (recorder - 1)) x with ⟨hN, -⟩ | ⟨U, hW, hS⟩
      · unfold untypedRecordsChild SystemState.getUntyped? at hw
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
            unfold untypedRecordsChild SystemState.getUntyped?; rw [hu]
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
      obtain ⟨i0, room0, -⟩ := retirePassiveObject_frame st (SeLe4n.ObjId.ofNat (target - 1)) hInv hSz
      have hT0 := retirePassiveObject_untypedRecordsChild st (SeLe4n.ObjId.ofNat (target - 1)) hInv hSz
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

theorem passiveObjectRetirable_parts {st : SystemState} {x : SeLe4n.ObjId}
    (h : passiveObjectRetirable st x = true) :
    passiveObjectQuiescent st x = true ∧ storeNamesNone st x = true ∧
      registryNamesNone st x = true ∧ servicesNameNone st x = true ∧
      irqHandlersNameNone st x = true := by
  unfold passiveObjectRetirable at h
  revert h
  cases passiveObjectQuiescent st x <;> cases storeNamesNone st x <;>
    cases registryNamesNone st x <;> cases servicesNameNone st x <;>
    cases irqHandlersNameNone st x <;> simp

/-- An admitted retire of a passive object retires one `passiveObjectRetirable`
admits. -/
theorem finalRetireAdmitted.retirable {st : SystemState} {x : SeLe4n.ObjId}
    (h : finalRetireAdmitted st x = true) (hP : passiveKernelObject st.objects[x]?) :
    passiveObjectRetirable st x = true := by
  unfold finalRetireAdmitted at h
  rw [(passiveKindAt_iff st x).mpr hP] at h
  simpa using h

/-- An empty slot array answers every lookup empty. -/
theorem CNode.lookup_none_of_cells_empty {cn : CNode} (h : cn.cells.all (·.isNone) = true)
    (s : SeLe4n.Slot) : cn.lookup s = none := by
  rw [CNode.lookup_eq_lookupCells]
  unfold CNode.lookupCells slotArrayGet
  split
  · next hs =>
    have := (Array.all_eq_true.mp h) s.toNat hs
    simpa using this
  · rfl

/-- **A quiescent passive object holds no capability**: only a CNode has slots
among the passive kinds, and a quiescent one has every slot empty. -/
theorem passiveObjectQuiescent.slotCap {st : SystemState} {x : SeLe4n.ObjId}
    (h : passiveObjectQuiescent st x = true) (o : KernelObject) (hO : st.objects[x]? = some o)
    (s : SeLe4n.Slot) : o.slotCap s = none := by
  unfold passiveObjectQuiescent SystemState.getObject? at h
  rw [hO] at h
  cases o with
  | cnode cn => exact CNode.lookup_none_of_cells_empty h s
  | _ => first | rfl | (simp at h)

/-- **The store scan answers per object**: no object the table resolves names
`x` (`RHTable.fold_and_true_of_get?`). -/
theorem storeNamesNone_spec {st : SystemState} {x : SeLe4n.ObjId} (h : storeNamesNone st x = true)
    {oid : SeLe4n.ObjId} {o : KernelObject} (hO : st.objects[oid]? = some o) :
    objectNamesById o x = false := by
  have := SeLe4n.Kernel.RobinHood.RHTable.fold_and_true_of_get? st.objects
    (fun _ o => !objectNamesById o x) h hO
  simpa using this

/-- **What a thread that does not name `x` does not do**: it is not blocked on
`x` in any state, not bound to it, and neither its reply link nor its stashed
reply is `x`. -/
theorem objectNamesById_tcb {t : TCB} {x : SeLe4n.ObjId}
    (h : objectNamesById (.tcb t) x = false) :
    (t.ipcState ≠ .blockedOnSend x ∧ t.ipcState ≠ .blockedOnReceive x ∧
      t.ipcState ≠ .blockedOnCall x ∧ t.ipcState ≠ .blockedOnNotification x ∧
      ∀ w, t.ipcState ≠ .blockedOnReply x w) ∧
    t.boundNotification ≠ some x ∧
    (∀ rid, t.replyObject = some rid → rid.toObjId ≠ x) ∧
    (∀ rid, t.pendingReceiveReply = some rid → rid.toObjId ≠ x) := by
  unfold objectNamesById at h
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨⟨⟨hI, hB⟩, hR⟩, hP⟩ := h
  have hSt : ∀ s : ThreadIpcState, ipcCodesName s.objectCode s.stateCode x = true →
      t.ipcState ≠ s := by
    intro s hs e
    obtain ⟨ho, hc⟩ := (TCB.ipcState_eq_iff_codes t s).mp e
    rw [ho, hc, hs] at hI; cases hI
  have hCode : ∀ (c : Nat) (rid : SeLe4n.ReplyId), SeLe4n.ReplyId.ofOptCode c = some rid →
      rid.toObjId = x → (c == x.val + 1) = true := by
    intro c rid hc hx
    have := congrArg SeLe4n.ReplyId.optCode hc
    rw [SeLe4n.ReplyId.optCode_ofOptCode] at this
    subst hx
    simp [this, SeLe4n.ReplyId.optCode, SeLe4n.ReplyId.toObjId, SeLe4n.ObjId.ofNat,
      SeLe4n.ReplyId.toNat]
  refine ⟨⟨hSt _ (by simp [ipcCodesName, ThreadIpcState.objectCode, ThreadIpcState.stateCode]),
    hSt _ (by simp [ipcCodesName, ThreadIpcState.objectCode, ThreadIpcState.stateCode]),
    hSt _ (by simp [ipcCodesName, ThreadIpcState.objectCode, ThreadIpcState.stateCode]),
    hSt _ (by simp [ipcCodesName, ThreadIpcState.objectCode, ThreadIpcState.stateCode]),
    fun w => hSt _ (by simp [ipcCodesName, ThreadIpcState.objectCode, ThreadIpcState.stateCode])⟩,
    fun e => ?_, fun rid hr hx => ?_, fun rid hr hx => ?_⟩
  · have := congrArg SeLe4n.ObjId.optCode e
    rw [SeLe4n.ObjId.optCode_ofOptCode] at this
    rw [this] at hB; simp [SeLe4n.ObjId.optCode] at hB
  · rw [hCode _ rid hr hx] at hR; cases hR
  · rw [hCode _ rid hr hx] at hP; cases hP

/-- **What a reply that does not name `x` does not link**: neither its stack
predecessor nor its successor is `x`. -/
theorem objectNamesById_reply {r : Reply} {x : SeLe4n.ObjId}
    (h : objectNamesById (.reply r) x = false) :
    (∀ p, r.prev = some p → p.toObjId ≠ x) ∧
      (∀ a, r.next = some (.frame a) → a.toObjId ≠ x) := by
  unfold objectNamesById at h
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨hp, hn⟩ := h
  refine ⟨fun p e hx => ?_, fun a e hx => ?_⟩
  · rw [e] at hp; simp [hx] at hp
  · rw [e] at hn; simp [hx] at hn

/-- A scheduling context that does not name `x` heads no reply stack at `x`. -/
theorem objectNamesById_schedContext {sc : SchedContext} {x : SeLe4n.ObjId}
    (h : objectNamesById (.schedContext sc) x = false) :
    ∀ r, sc.scReply = some r → r.toObjId ≠ x := by
  intro r e hx
  have h' : (match sc.scReply with | some r => r.toObjId == x | none => false) = false := h
  rw [e] at h'; simp [hx] at h'

/-- The passive erase of a passive object leaves its key empty. -/
theorem retirePassiveObject_self {st : SystemState} {x : SeLe4n.ObjId}
    (hP : passiveKernelObject st.objects[x]?) (hInv : st.objects.invExt) :
    (retirePassiveObject st x).objects[x]? = none := by
  unfold retirePassiveObject
  rw [if_pos ((passiveKindAt_iff st x).mpr hP)]
  exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_self st.objects x hInv

/-- **After the passive erase no passive object stands at `x`.** -/
theorem retirePassiveObject_not_passive (st : SystemState) (x : SeLe4n.ObjId)
    (hInv : st.objects.invExt) : ¬ passiveKernelObject (retirePassiveObject st x).objects[x]? := by
  by_cases hP0 : passiveKernelObject st.objects[x]?
  · rw [retirePassiveObject_self hP0 hInv]; exact fun h => h
  · rw [retirePassiveObject_of_not st x hP0]; exact hP0

/-- **A retire write at a key holding no passive object touches only what a
reset touches.** -/
theorem finalRetireWrite.resetTouched {st st' : SystemState} {x : SeLe4n.ObjId}
    (h : finalRetireWrite st st' x) (hNP : ¬ passiveKernelObject st.objects[x]?)
    (oid : SeLe4n.ObjId) :
    st'.objects[oid]? = st.objects[oid]? ∨
      (resetTouched st.objects[oid]? ∧ resetTouched st'.objects[oid]?) := by
  rcases h oid with e | ⟨hx, hcp, hn⟩ | ⟨U, hU, hU'⟩
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
            (retirePassiveObject st (SeLe4n.ObjId.ofNat (target - 1)))) := by
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
        (∀ t, st.objects[oid]? ≠ some (.tcb t)) ∧
        ((retireFinalObject ec target recorder st).objects[oid]? = none ∨
          ∃ U, (retireFinalObject ec target recorder st).objects[oid]? = some (.untyped U))) := by
  rcases retireFinalObject_admitted ec target recorder st with hE | hAdm
  · rw [hE]; exact .inl rfl
  have hW := (retireFinalObject_frame ec target recorder st hInv).2.2.2.2
  generalize retireFinalObject ec target recorder st = st' at hW ⊢
  rcases hW oid with e | ⟨hxo, hcp, hn⟩ | ⟨U, hU, hU'⟩
  · exact .inl e
  · refine .inr ⟨?_, ?_, .inl hn⟩
    · intro o hO s
      rcases hcp with (⟨f, hf⟩ | ⟨u, hu⟩ | ⟨r, hr⟩ | ⟨p, hp⟩) | hp
      · rw [hf] at hO; cases hO; rfl
      · rw [hu] at hO; cases hO; rfl
      · rw [hr] at hO; cases hO; rfl
      · rw [hp] at hO; cases hO; rfl
      · subst hxo
        exact passiveObjectQuiescent.slotCap
          (passiveObjectRetirable_parts (finalRetireAdmitted.retirable hAdm hp)).1 o hO s
    · intro t hT
      rcases hcp with (⟨f, hf⟩ | ⟨u, hu⟩ | ⟨r, hr⟩ | ⟨p, hp⟩) | hp
      · rw [hf] at hT; cases hT
      · rw [hu] at hT; cases hT
      · rw [hr] at hT; cases hT
      · rw [hp] at hT; cases hT
      · rw [hT] at hp; exact hp
  · exact .inr ⟨fun o hO s => (by rw [hU] at hO; cases hO; rfl),
      fun t hT => (by rw [hU] at hT; cases hT), .inr ⟨_, hU'⟩⟩

/-- **The retire keeps every thread**, key by key. -/
theorem retireFinalObject_tcb_iff (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) (oid : SeLe4n.ObjId) (t : TCB) :
    (retireFinalObject ec target recorder st).objects[oid]? = some (.tcb t) ↔
      st.objects[oid]? = some (.tcb t) := by
  rcases retireFinalObject_key ec target recorder st hInv oid with e | ⟨-, hNT, hn | ⟨U, hU⟩⟩
  · rw [e]
  · rw [hn]; exact ⟨fun h => (by cases h), fun h => absurd h (hNT t)⟩
  · rw [hU]; exact ⟨fun h => (by cases h), fun h => absurd h (hNT t)⟩

theorem retireFinalObject_getTcb? (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) :
    (retireFinalObject ec target recorder st).getTcb? = st.getTcb? := by
  funext tid
  cases h : st.getTcb? tid with
  | some t =>
    exact (SystemState.getTcb?_eq_some_iff _ tid t).mpr
      ((retireFinalObject_tcb_iff ec target recorder st hInv _ t).mpr
        ((SystemState.getTcb?_eq_some_iff st tid t).mp h))
  | none =>
    cases h' : (retireFinalObject ec target recorder st).getTcb? tid with
    | none => rfl
    | some t =>
      have := (retireFinalObject_tcb_iff ec target recorder st hInv _ t).mp
        ((SystemState.getTcb?_eq_some_iff _ tid t).mp h')
      rw [(SystemState.getTcb?_eq_some_iff st tid t).mpr this] at h; cases h

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
  unfold SystemState.lookupSlotCap SystemState.lookupCNode
  rcases retireFinalObject_key ec target recorder st hInv r.cnode with e | ⟨hb, -, ha⟩
  · rw [e]
  · have hR : (match st.objects[r.cnode]? with
        | some (.cnode cn) => some cn | _ => none).bind (fun cn => cn.lookup r.slot) = none := by
      cases hs : st.objects[r.cnode]? with
      | none => rfl
      | some o =>
        cases o with
        | cnode cn => exact hb _ hs r.slot
        | _ => rfl
    rcases ha with hn | ⟨U, hU⟩
    all_goals
      first | rw [hn] | rw [hU]
      revert hR
      cases st.objects[r.cnode]? with
      | none => intro _; rfl
      | some o => cases o <;> simp <;> exact fun h => h.symm

/-- **The retire makes no untyped**: a key that held none holds none after. -/
theorem retireFinalObject_getUntyped?_none (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {u : SeLe4n.ObjId}
    (h : st.getUntyped? u = none) :
    (retireFinalObject ec target recorder st).getUntyped? u = none := by
  rw [SystemState.getUntyped?_eq_bind] at h ⊢
  rcases (retireFinalObject_frame ec target recorder st hInv).2.2.2.2 u with e | ⟨-, -, hn⟩ | ⟨U, hU, -⟩
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

theorem unrecordChild_asidTable (st : SystemState) (w x : SeLe4n.ObjId) :
    (unrecordChild st w x).asidTable = st.asidTable := by
  rcases unrecordChild_cases st w x with ⟨-, hE⟩ | ⟨U, hW, hS⟩
  · rw [hE]
  · rw [storeObject_asidTable_non_vspaceRoot _ _ _ _ (fun _ h => by cases h) hS, hW]

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

/-- **The passive erase keeps the teardown's state well formed and keeps every
root**: a passive object is no root, and the ASID table is not written. -/
theorem retirePassiveObject_preserves_teardownWellFormed (st : SystemState) (x : SeLe4n.ObjId)
    (hW : teardownWellFormed st) (hSz : st.objects.size < st.objects.capacity) :
    teardownWellFormed (retirePassiveObject st x) ∧ vspaceRootsShrink st (retirePassiveObject st x) := by
  obtain ⟨hI, -, -, -, -, hA, -, -⟩ := retirePassiveObject_frame st x hW.1 hSz
  have hR : ∀ (oid : SeLe4n.ObjId) (r : VSpaceRoot),
      (retirePassiveObject st x).objects[oid]? = some (KernelObject.vspaceRoot r) ↔
        st.objects[oid]? = some (KernelObject.vspaceRoot r) := by
    intro oid r
    rcases retirePassiveObject_write st x hW.1 hSz oid with e | ⟨-, hp, hn⟩
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
(`retirePassiveObject_preserves_teardownWellFormed`), and the recorded retire
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
    · obtain ⟨hW0, hS0⟩ := retirePassiveObject_preserves_teardownWellFormed st _ hW hSz
      obtain ⟨-, room0, -⟩ := retirePassiveObject_frame st (SeLe4n.ObjId.ofNat (target - 1)) hW.1 hSz
      obtain ⟨hW1, hS1⟩ := retireRecordedObject_preserves_teardownWellFormed ec recorder _ _ hW0 room0
      exact ⟨hW1, hS0.trans hS1⟩
    · exact ⟨hW, vspaceRootsShrink.refl st⟩
  · exact ⟨hW, vspaceRootsShrink.refl st⟩

/-- A retire of nothing is the identity. -/
theorem retireFinalObject_zero (ec : Concurrency.CoreId) (recorder : Nat) (st : SystemState) :
    retireFinalObject ec 0 recorder st = st := by
  unfold retireFinalObject; rfl

theorem retirePassiveObject_fields (st : SystemState) (x : SeLe4n.ObjId) :
    (retirePassiveObject st x).cdt = st.cdt ∧
    (retirePassiveObject st x).scheduler = st.scheduler ∧
    (retirePassiveObject st x).machine = st.machine := by
  unfold retirePassiveObject; split <;> exact ⟨rfl, rfl, rfl⟩

theorem retireRecordedObject_fields (ec : Concurrency.CoreId) (recorder : Nat) (x : SeLe4n.ObjId)
    (st : SystemState) :
    (retireRecordedObject ec recorder x st).cdt = st.cdt ∧
    (retireRecordedObject ec recorder x st).scheduler = st.scheduler ∧
    (retireRecordedObject ec recorder x st).machine = st.machine := by
  unfold retireRecordedObject
  dsimp only
  have h1 : (if recorder = 0 then st
      else unrecordChild st (SeLe4n.ObjId.ofNat (recorder - 1)) x).cdt = st.cdt ∧
      (if recorder = 0 then st
      else unrecordChild st (SeLe4n.ObjId.ofNat (recorder - 1)) x).scheduler = st.scheduler ∧
      (if recorder = 0 then st
      else unrecordChild st (SeLe4n.ObjId.ofNat (recorder - 1)) x).machine = st.machine := by
    split
    · exact ⟨rfl, rfl, rfl⟩
    · rcases unrecordChild_cases st (SeLe4n.ObjId.ofNat (recorder - 1)) x with ⟨-, hE⟩ | ⟨U, -, hS⟩
      · rw [hE]; exact ⟨rfl, rfl, rfl⟩
      · exact ⟨storeObject_cdt_eq _ _ _ _ hS, storeObject_scheduler_eq _ _ _ _ hS,
          storeObject_machine_eq _ _ _ _ hS⟩
  generalize (if recorder = 0 then st
      else unrecordChild st (SeLe4n.ObjId.ofNat (recorder - 1)) x) = st1 at h1
  obtain ⟨s2, m2, c2⟩ := retireCarvedObject_scheduler_machine_cdt st1 x
  split
  · rw [retypeAsidRoundStep_cdt, retypeAsidRoundStep_scheduler, retypeAsidRoundStep_machine,
      c2, s2, m2]
    exact h1
  · rw [c2, s2, m2]; exact h1

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
    · obtain ⟨c0, s0, m0⟩ := retirePassiveObject_fields st (SeLe4n.ObjId.ofNat (target - 1))
      obtain ⟨c1, s1, m1⟩ := retireRecordedObject_fields ec recorder (SeLe4n.ObjId.ofNat (target - 1))
        (retirePassiveObject st (SeLe4n.ObjId.ofNat (target - 1)))
      exact ⟨c1.trans c0, s1.trans s0, m1.trans m0⟩
    · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

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

theorem untypedWithoutChild_of_not_records {U : UntypedObject} {x : SeLe4n.ObjId}
    (h : childListRecords U.children x = false) : untypedWithoutChild U x = U := by
  unfold untypedWithoutChild; rw [childListErase_of_not_records h]

/-- **The retire keeps every key a predicate admits**, when the predicate admits
neither the target nor any untyped recording it. -/
theorem retireFinalObject_objects_of_excluded (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) (p : SeLe4n.ObjId → Bool)
    (hx : target ≠ 0 → p (SeLe4n.ObjId.ofNat (target - 1)) = false)
    (hU : target ≠ 0 → ∀ w, untypedRecordsChild st w (SeLe4n.ObjId.ofNat (target - 1)) = true →
      p w = false)
    (o : SeLe4n.ObjId) (ho : p o = true) :
    (retireFinalObject ec target recorder st).objects[o]? = st.objects[o]? := by
  by_cases h0 : target = 0
  · rw [h0, retireFinalObject_zero]
  rcases (retireFinalObject_frame ec target recorder st hInv).2.2.2.2 o with
    e | ⟨hxo, -, -⟩ | ⟨U, hU0, hU1⟩
  · exact e
  · subst hxo; rw [hx h0] at ho; cases ho
  · have hr : childListRecords U.children (SeLe4n.ObjId.ofNat (target - 1)) = false := by
      cases hc : childListRecords U.children (SeLe4n.ObjId.ofNat (target - 1)) with
      | false => rfl
      | true =>
        have hrec : untypedRecordsChild st o (SeLe4n.ObjId.ofNat (target - 1)) = true := by
          unfold untypedRecordsChild
          rw [(SystemState.getUntyped?_eq_some_iff st o U).mpr hU0]; exact hc
        rw [hU h0 o hrec] at ho; cases ho
    rw [hU1, hU0, untypedWithoutChild_of_not_records hr]

/-- **The retire records no new child**: an untyped that records `o` after it
recorded `o` before. -/
theorem retireFinalObject_untypedRecordsChild (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {w o : SeLe4n.ObjId}
    (h : untypedRecordsChild (retireFinalObject ec target recorder st) w o = true) :
    untypedRecordsChild st w o = true := by
  unfold untypedRecordsChild at h ⊢
  cases hA : (retireFinalObject ec target recorder st).getUntyped? w with
  | none => rw [hA] at h; cases h
  | some U' =>
    rw [hA] at h
    dsimp only at h
    have hA' := (SystemState.getUntyped?_eq_some_iff _ w U').mp hA
    rcases (retireFinalObject_frame ec target recorder st hInv).2.2.2.2 w with
      e | ⟨-, -, hn⟩ | ⟨U, hU0, hU1⟩
    · rw [e] at hA'; rw [(SystemState.getUntyped?_eq_some_iff st w U').mpr hA']; exact h
    · rw [hn] at hA'; cases hA'
    · rw [hU1] at hA'
      cases hA'
      rw [(SystemState.getUntyped?_eq_some_iff st w U).mpr hU0]
      dsimp only
      simp only [untypedWithoutChild] at h
      obtain ⟨ch, hm, he⟩ := (childListRecords_iff _ _).mp h
      exact (childListRecords_iff _ _).mpr ⟨ch, (mem_childListErase.mp hm).1, he⟩

theorem filter_bne_filter {l : List SeLe4n.ObjId} {x : SeLe4n.ObjId} {p : SeLe4n.ObjId → Bool}
    (hx : p x = false) : (l.filter (· != x)).filter p = l.filter p := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    by_cases h : a = x
    · subst h; simp [List.filter_cons, hx, ih]
    · simp [List.filter_cons, h, ih]

/-- **The retire keeps the service and interrupt tables, and the object index
on the keys a predicate admits**, when the predicate admits neither the target
nor the recorder. -/
theorem retireFinalObject_tables (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (p : SeLe4n.ObjId → Bool)
    (hx : target ≠ 0 → p (SeLe4n.ObjId.ofNat (target - 1)) = false)
    (hR : recorder ≠ 0 → p (SeLe4n.ObjId.ofNat (recorder - 1)) = false) :
    (retireFinalObject ec target recorder st).services = st.services ∧
    (retireFinalObject ec target recorder st).irqHandlers = st.irqHandlers ∧
    (retireFinalObject ec target recorder st).objectIndex.filter p = st.objectIndex.filter p := by
  unfold retireFinalObject
  split
  · exact ⟨rfl, rfl, rfl⟩
  next h0 =>
  split
  · dsimp only
    split
    · have h1 : (retirePassiveObject st (SeLe4n.ObjId.ofNat (target - 1))).services = st.services ∧
          (retirePassiveObject st (SeLe4n.ObjId.ofNat (target - 1))).irqHandlers = st.irqHandlers ∧
          (retirePassiveObject st (SeLe4n.ObjId.ofNat (target - 1))).objectIndex.filter p =
            st.objectIndex.filter p := by
        unfold retirePassiveObject
        split
        · exact ⟨rfl, rfl, filter_bne_filter (hx h0)⟩
        · exact ⟨rfl, rfl, rfl⟩
      generalize retirePassiveObject st (SeLe4n.ObjId.ofNat (target - 1)) = s0 at h1 ⊢
      unfold retireRecordedObject
      dsimp only
      have h2 : (if recorder = 0 then s0
            else unrecordChild s0 (SeLe4n.ObjId.ofNat (recorder - 1)) (SeLe4n.ObjId.ofNat (target - 1))).services
              = st.services ∧
          (if recorder = 0 then s0
            else unrecordChild s0 (SeLe4n.ObjId.ofNat (recorder - 1)) (SeLe4n.ObjId.ofNat (target - 1))).irqHandlers
              = st.irqHandlers ∧
          (if recorder = 0 then s0
            else unrecordChild s0 (SeLe4n.ObjId.ofNat (recorder - 1))
              (SeLe4n.ObjId.ofNat (target - 1))).objectIndex.filter p = st.objectIndex.filter p := by
        split
        · exact h1
        · next hr =>
          rcases unrecordChild_cases s0 (SeLe4n.ObjId.ofNat (recorder - 1))
              (SeLe4n.ObjId.ofNat (target - 1)) with ⟨-, hE⟩ | ⟨U, -, hS⟩
          · rw [hE]; exact h1
          · unfold storeObject at hS
            simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
            rw [← hS]
            refine ⟨h1.1, h1.2.1, ?_⟩
            dsimp only
            split
            · exact h1.2.2
            · rw [List.filter_cons, hR hr]; exact h1.2.2
      generalize (if recorder = 0 then s0
          else unrecordChild s0 (SeLe4n.ObjId.ofNat (recorder - 1))
            (SeLe4n.ObjId.ofNat (target - 1))) = s1 at h2 ⊢
      have h3 : (retireCarvedObject s1 (SeLe4n.ObjId.ofNat (target - 1))).services = st.services ∧
          (retireCarvedObject s1 (SeLe4n.ObjId.ofNat (target - 1))).irqHandlers = st.irqHandlers ∧
          (retireCarvedObject s1 (SeLe4n.ObjId.ofNat (target - 1))).objectIndex.filter p =
            st.objectIndex.filter p := by
        unfold retireCarvedObject
        split
        · exact ⟨h2.1, h2.2.1, (filter_bne_filter (hx h0)).trans h2.2.2⟩
        · exact h2
      split
      · exact h3
      · exact h3
    · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
