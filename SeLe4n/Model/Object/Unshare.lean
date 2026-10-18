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

/-- `KernelObject.unshare` as compiled.  Each record is rebuilt with one field
passed through `opaqueId`, so a shared record is copied and an exclusive one
written in place; a thread's register file, a CNode's slot array and a VSpace
root's mapping and epoch tables are rebuilt the same way. -/
def KernelObject.unshareImpl : KernelObject → KernelObject
  | .tcb t => .tcb { t with
      tid := opaqueId t.tid
      registerContext := { t.registerContext with x0 := opaqueId t.registerContext.x0 } }
  | .endpoint e => .endpoint { e with sendHeadCode := opaqueId e.sendHeadCode }
  | .notification n => .notification { n with state := opaqueId n.state }
  | .cnode c => .cnode { c with
      depth := opaqueId c.depth
      cells := c.cells.map opaqueId
      cells_size := by rw [Array.size_map]; exact c.cells_size
      slots_agree := by
        have h : (opaqueId : Option Capability → Option Capability) = id := rfl
        rw [h, Array.map_id]; exact c.slots_agree
      links := c.links.map opaqueId
      links_size := by rw [Array.size_map]; exact c.links_size }
  | .vspaceRoot v => .vspaceRoot { v with
      asid := opaqueId v.asid
      mappings := v.mappings.unshare
      mappingEpochs := v.mappingEpochs.unshare }
  | .untyped u => .untyped { u with regionBase := opaqueId u.regionBase }
  | .schedContext sc => .schedContext { sc with scId := opaqueId sc.scId }
  | .reply r => .reply { r with replyId := opaqueId r.replyId }
  | .frame f => .frame { f with base := opaqueId f.base }
  | .pageTable p => .pageTable { p with base := opaqueId p.base }

@[csimp] theorem KernelObject.unshare_eq_impl :
    @KernelObject.unshare = @KernelObject.unshareImpl := by
  funext o
  have hId : (opaqueId : Option Capability → Option Capability) = id := rfl
  have hIdN : (opaqueId : Nat → Nat) = id := rfl
  cases o <;>
    simp only [KernelObject.unshare, KernelObject.unshareImpl, hId, hIdN, Array.map_id, opaqueId,
      RHTable.unshare]

end SeLe4n.Model
