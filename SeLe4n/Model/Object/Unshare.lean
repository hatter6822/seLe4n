/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Model.Object.Structures

/-!
# Objects that enter the store own their cells

WS-ZA.  An object built from constant fields (a boot image's initial objects,
the default object a retype creates) is a closed term: the compiled kernel
holds it as one shared static value, so the first in-place write to it (a
signal's pending badge, a send's queue end) finds it shared and copies it.
`KernelObject.unshare` is the identity in the specification; as compiled
(`unshare_eq_impl`) it rebuilds the object's record, and the register file,
slot table or mapping and epoch tables an in-place write reaches, into cells nobody else
holds, so that copy happens once where the object enters the store and never
on a syscall.
-/

namespace SeLe4n.Model

open SeLe4n.Kernel.RobinHood

/-- The identity, kept out of the compiler's sight so that a record rebuilt
through it is a fresh cell when the record was shared (the compiler turns a
record rebuilt from its own projections back into the record itself). -/
@[noinline] def opaqueId {α : Type _} (a : α) : α := a

/-- The identity: a table whose slot array is copied when shared. -/
def _root_.SeLe4n.Kernel.RobinHood.RHTable.unshare {α β : Type} (t : RHTable α β) : RHTable α β := t

/-- `RHTable.unshare` as compiled: the slot array rebuilt through `opaqueId`,
which copies it when shared and writes it in place when not. -/
def _root_.SeLe4n.Kernel.RobinHood.RHTable.unshareImpl {α β : Type} (t : RHTable α β) : RHTable α β :=
  { t with
    slots := t.slots.map opaqueId
    hSlotsLen := by rw [Array.size_map]; exact t.hSlotsLen }

theorem _root_.SeLe4n.Kernel.RobinHood.RHTable.unshareImpl_eq {α β : Type} (t : RHTable α β) :
    t.unshareImpl = t := by
  cases t
  have h : (opaqueId : Option (RHEntry α β) → Option (RHEntry α β)) = id := rfl
  simp [RHTable.unshareImpl, h]

@[csimp] theorem _root_.SeLe4n.Kernel.RobinHood.RHTable.unshare_eq_impl :
    @RHTable.unshare = @RHTable.unshareImpl := by
  funext α β t
  exact (RHTable.unshareImpl_eq t).symm

/-- The identity: an object whose cells are rebuilt when shared. -/
def KernelObject.unshare (o : KernelObject) : KernelObject := o

@[simp] theorem KernelObject.unshare_eq (o : KernelObject) : o.unshare = o := rfl

/-- A CNode's spare record, rebuilt when shared so each slot owns its own
(WS-ZA ZA5.3 part 6). -/
@[inline] def unshareSpareCell (o : Option Capability) : Option Capability :=
  match o with
  | some r => some { r with rights := opaqueId r.rights }
  | none => none

/-- A CNode's slot cell, rebuilt when shared so the CNode owns its `some` and its
capability record: since WS-ZA ZA5.4 part 13 a carve writes the invoked untyped
capability's free index into that record in place (`CNode.setFreeIndexCells`),
and a boot capability's record is otherwise the boot image's constant, so the
first carve would copy both. -/
@[inline] def unshareSlotCell (o : Option Capability) : Option Capability :=
  match o with
  | some r => some { r with rights := opaqueId r.rights }
  | none => none

theorem unshareSlotCell_eq (o : Option Capability) : unshareSlotCell o = o := by
  cases o with
  | none => rfl
  | some r => simp only [unshareSlotCell, opaqueId]

/-- A thread's space slot, rebuilt when shared so the thread owns its `some` and
its capability record (`spaceCellOver`, setting the thread's space, writes both
in place). -/
@[inline] def unshareSpaceCell (o : Option Capability) : Option Capability :=
  match o with
  | some r => some { r with rights := opaqueId r.rights }
  | none => none

theorem unshareSpaceCell_eq (o : Option Capability) : unshareSpaceCell o = o := by
  cases o with
  | none => rfl
  | some r => simp only [unshareSpaceCell, opaqueId]

/-- A VSpace root's spare mapping cell, rebuilt when shared so the root owns
its `some`, its entry and the entry's value pair (WS-ZA ZA5.4). -/
@[inline] def unshareMappingCell
    (o : Option (RHEntry SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions))) :
    Option (RHEntry SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions)) :=
  match o with
  | some e => some { e with value := (opaqueId e.value.1, e.value.2) }
  | none => none

/-- A VSpace root's spare epoch cell, rebuilt when shared (WS-ZA ZA5.4). -/
@[inline] def unshareEpochCell (o : Option (RHEntry SeLe4n.VAddr Nat)) :
    Option (RHEntry SeLe4n.VAddr Nat) :=
  match o with
  | some e => some { e with dist := opaqueId e.dist }
  | none => none

/-- A page table's slot cell, rebuilt when shared so the table owns its list
cell and its slot record (WS-ZA ZA5.4). -/
@[inline] def unshareTableSlot (s : PageTableSlot) : PageTableSlot :=
  { s with level := opaqueId s.level }

/-- `KernelObject.unshare` as compiled.  Each record is rebuilt with one field
passed through `opaqueId`, so a shared record is copied and an exclusive one
written in place; a thread's register file, a CNode's slot array and its slot
records, a VSpace root's mapping and epoch tables and their spare cells, and a
page table's slot
cell, are rebuilt the same way. -/
def KernelObject.unshareImpl : KernelObject → KernelObject
  | .tcb t => .tcb { t with
      tid := opaqueId t.tid
      spaceCells := t.spaceCells.map unshareSpaceCell
      spaceLinks := t.spaceLinks.map opaqueId
      registerContext := { t.registerContext with x0 := opaqueId t.registerContext.x0 } }
  | .endpoint e => .endpoint { e with sendHeadCode := opaqueId e.sendHeadCode }
  | .notification n => .notification { n with state := opaqueId n.state }
  | .cnode c => .cnode { c with
      depth := opaqueId c.depth
      cells := c.cells.map unshareSlotCell
      cells_size := by rw [Array.size_map]; exact c.cells_size
      slots_agree := by
        have h : unshareSlotCell = id := funext unshareSlotCell_eq
        rw [h, Array.map_id]; exact c.slots_agree
      links := c.links.map opaqueId
      links_size := by rw [Array.size_map]; exact c.links_size
      spare := Quot.lift (fun a => Squash.mk (a.map unshareSpareCell))
        (fun _ _ _ => Subsingleton.elim _ _) c.spare }
  | .vspaceRoot v => .vspaceRoot { v with
      asid := opaqueId v.asid
      mappings := v.mappings.unshare
      mappingEpochs := v.mappingEpochs.unshare
      mappingSpare := Quot.lift (fun a => Squash.mk (unshareMappingCell a))
        (fun _ _ _ => Subsingleton.elim _ _) v.mappingSpare
      epochSpare := Quot.lift (fun a => Squash.mk (unshareEpochCell a))
        (fun _ _ _ => Subsingleton.elim _ _) v.epochSpare }
  | .untyped u => .untyped { u with regionBase := opaqueId u.regionBase }
  | .schedContext sc => .schedContext { sc with scId := opaqueId sc.scId }
  | .reply r => .reply { r with replyId := opaqueId r.replyId }
  | .frame f => .frame { f with base := opaqueId f.base }
  | .pageTable p => .pageTable { p with
      base := opaqueId p.base
      slotCell := Quot.lift (fun a => Squash.mk (a.map unshareTableSlot))
        (fun _ _ _ => Subsingleton.elim _ _) p.slotCell }

@[csimp] theorem KernelObject.unshare_eq_impl :
    @KernelObject.unshare = @KernelObject.unshareImpl := by
  funext o
  have hId : (opaqueId : Option Capability → Option Capability) = id := rfl
  have hIdN : (opaqueId : Nat → Nat) = id := rfl
  cases o
  case cnode c =>
    have hC : unshareSlotCell = id := funext unshareSlotCell_eq
    simp only [KernelObject.unshare, KernelObject.unshareImpl, hC, hId, hIdN, Array.map_id, opaqueId,
      KernelObject.cnode.injEq]
    exact CNode.ext_of_fields rfl rfl rfl rfl rfl rfl rfl
  case vspaceRoot v =>
    simp only [KernelObject.unshare, KernelObject.unshareImpl, opaqueId, RHTable.unshare,
      KernelObject.vspaceRoot.injEq]
    cases v
    simp only [VSpaceRoot.mk.injEq, true_and, and_true]
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  case pageTable p =>
    simp only [KernelObject.unshare, KernelObject.unshareImpl, opaqueId,
      PageTableObject.with_slotCell]
  case tcb t =>
    have hS : unshareSpaceCell = id := funext unshareSpaceCell_eq
    simp only [KernelObject.unshare, KernelObject.unshareImpl, hS, hIdN, Vector.map_id, opaqueId]
  all_goals
    simp only [KernelObject.unshare, KernelObject.unshareImpl, hId, hIdN, Array.map_id, opaqueId,
      RHTable.unshare]

/-- **An object built from constant fields, given its own cells where it is
built**: the identity (`unshare`).  A carve's default endpoint or notification
is a closed term, which the compiler hoists to one shared static value, and a
call of `unshare` on a closed term is itself a closed term it would hoist.
`never_extract` keeps this call where it is written, so the rebuild it compiles
to (`unshareImpl`) runs on every carve and the first in-place write to the
object finds it unshared. -/
@[noinline, never_extract] def KernelObject.unshareFresh (o : KernelObject) : KernelObject :=
  o.unshare

@[simp] theorem KernelObject.unshareFresh_eq (o : KernelObject) : o.unshareFresh = o := rfl

end SeLe4n.Model
