-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-! # The tables that name objects by id, and the objects' back-links to them

Three tables of the state name kernel objects by id outside every slot: the
service registry (a registration keeps its endpoint's capability), the
interrupt-handler table (an interrupt names the notification it signals) and
the service graph (an entry names its backing object and its owner).  A
capability held there is one the derivation tree does not see, so a final
delete must not retire an object a table still names.

seL4 has no service registry or service graph, and keeps an interrupt's
notification capability in the interrupt's own slot, where finality sees it.
Here each table reference is answered by the object, as seL4's objects answer
the references to them:

* a registration is recorded on its endpoint (`Endpoint.serviceCode`, written
  by `registerService` and cleared by `revokeService`);
* an interrupt handler is recorded on its notification (`Notification.irqBound`,
  set by the boot for every notification the interrupt table names; nothing
  after the boot writes the table);
* the service graph holds no entry (`RHTable.slotsEmpty`): no kernel entry
  writes it, so it stays as the boot leaves it, empty.

`tableReferencesRecorded` states all three, each with its converse, and
`tableBackLinksClear` reads an object's own back-links in place of a walk of
the three tables; `tableBackLinksClear.namedByNone` is the theorem that, under
`tableReferencesRecorded`, an object it admits is named by no table entry — the
consumer theorem that makes the back-links worth recording.

The final delete reads the back-links instead of walking the tables (WS-ZA
ZA5.4 part 31): the boot establishes `tableReferencesRecorded`, and every step
that writes no table and leaves every object's back-links as it found them is a
`TableReferenceFrame`, the form in which the run-queue link stage carries the
invariant through every syscall and kernel entry. -/

namespace SeLe4n.Kernel.RobinHood

variable {α β γ : Type}

/-- **A table no slot of which holds an entry.** -/
def RHTable.slotsEmpty (t : RHTable α β) : Prop :=
  ∀ (i : Nat) (h : i < t.slots.size), t.slots[i] = none

theorem getLoop_of_slotsEmpty [BEq α] [Hashable α] (fuel idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β))) (cap : Nat) (hLen : slots.size = cap)
    (hCap : 0 < cap) (hE : ∀ (i : Nat) (h : i < slots.size), slots[i] = none) :
    getLoop fuel idx k d slots cap hLen hCap = none := by
  cases fuel with
  | zero => rfl
  | succ n => unfold getLoop; simp only [hE]

theorem findLoop_of_slotsEmpty [BEq α] [Hashable α] (fuel idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β))) (cap : Nat) (hLen : slots.size = cap)
    (hCap : 0 < cap) (hE : ∀ (i : Nat) (h : i < slots.size), slots[i] = none) :
    findLoop fuel idx k d slots cap hLen hCap = none := by
  cases fuel with
  | zero => rfl
  | succ n => unfold findLoop; simp only [hE]

/-- An empty table looks nothing up. -/
theorem RHTable.get?_of_slotsEmpty [BEq α] [Hashable α] [LawfulBEq α] {t : RHTable α β}
    (h : t.slotsEmpty) (k : α) : t.get? k = none :=
  getLoop_of_slotsEmpty _ _ _ _ _ _ _ _ h

/-- An empty table erases nothing. -/
theorem RHTable.erase_of_slotsEmpty [BEq α] [Hashable α] [LawfulBEq α] {t : RHTable α β}
    (h : t.slotsEmpty) (k : α) : t.erase k = t := by
  unfold RHTable.erase
  simp only [findLoop_of_slotsEmpty _ _ _ _ _ _ _ _ h]

/-- A fold over an empty table is its initial value. -/
theorem RHTable.fold_of_slotsEmpty {t : RHTable α β} (h : t.slotsEmpty) (init : γ)
    (f : γ → α → β → γ) : t.fold init f = init := by
  unfold RHTable.fold
  rw [← Array.foldl_toList]
  have hL : ∀ x ∈ t.slots.toList, x = none := fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [Array.getElem_toList]
    exact h i (by simpa using hi)
  clear h
  generalize t.slots.toList = L at hL
  induction L generalizing init with
  | nil => rfl
  | cons x xs ih =>
    rw [hL x List.mem_cons_self]
    exact ih init (fun y hy => hL y (List.mem_cons_of_mem _ hy))

/-- The empty table of any capacity is empty. -/
theorem RHTable.empty_slotsEmpty (cap : Nat) (hCapGe4 : 4 ≤ cap) :
    (RHTable.empty cap hCapGe4 : RHTable α β).slotsEmpty := fun i hi => by
  simp [RHTable.empty]

end SeLe4n.Kernel.RobinHood

namespace SeLe4n.Model

open SeLe4n.Kernel.RobinHood

/-- The table back-links an object slot holds; an empty slot holds none. -/
@[inline] def objTableBackLinks : Option KernelObject → Nat × Bool
  | some o => o.tableBackLinks
  | none => (0, false)

@[simp] theorem objTableBackLinks_none : objTableBackLinks none = (0, false) := rfl

@[simp] theorem objTableBackLinks_some (o : KernelObject) :
    objTableBackLinks (some o) = o.tableBackLinks := rfl

/-- The back-links of a slot, read off the object the slot maps to. -/
theorem objTableBackLinks_eq_map (o : Option KernelObject) :
    objTableBackLinks o = (o.map KernelObject.tableBackLinks).getD (0, false) := by
  cases o <;> rfl

/-- The three tables that name objects by id outside every slot. -/
@[inline] def SystemState.referenceTables (st : SystemState) :
    RHTable ServiceId ServiceRegistration × RHTable SeLe4n.Irq SeLe4n.ObjId ×
      RHTable ServiceId ServiceGraphEntry :=
  (st.serviceRegistry, st.irqHandlers, st.services)

/-- **Every table reference by id is recorded on the object it names, and
every back-link an object holds answers a table entry.**  A registration names
an endpoint whose code is its service's (`registry`), and an endpoint's code
names a registration of it (`serviceCodes`); an interrupt names a notification
whose flag is set (`irqHandlers`), and a set flag is named by an interrupt
(`irqBound`); the service graph holds no entry (`servicesEmpty`).  Established
by the boot and kept by every syscall and kernel entry (the run-queue stages
carry it, `SystemState.RunQueueLinkStage`), so a final delete reads the object
it retires (`tableBackLinksClear`) instead of walking the tables. -/
structure SystemState.tableReferencesRecorded (st : SystemState) : Prop where
  /-- The registry's table invariant, which its erase reads. -/
  registryInvExtK : st.serviceRegistry.invExtK
  /-- A registration names an endpoint recording its service. -/
  registry : ∀ (sid : ServiceId) (reg : ServiceRegistration),
    st.serviceRegistry[sid]? = some reg →
    ∃ e, reg.endpointCap.target = .object e ∧ (objTableBackLinks st.objects[e]?).1 = sid.val + 1
  /-- An endpoint's registration code names a registration of it. -/
  serviceCodes : ∀ (e : SeLe4n.ObjId) (n : Nat), (objTableBackLinks st.objects[e]?).1 = n + 1 →
    ∃ reg, st.serviceRegistry[(⟨n⟩ : ServiceId)]? = some reg ∧ reg.endpointCap.target = .object e
  /-- An interrupt names a notification recording it. -/
  irqHandlers : ∀ (irq : SeLe4n.Irq) (n : SeLe4n.ObjId), st.irqHandlers[irq]? = some n →
    (objTableBackLinks st.objects[n]?).2 = true
  /-- A notification's interrupt flag is named by an interrupt. -/
  irqBound : ∀ n : SeLe4n.ObjId, (objTableBackLinks st.objects[n]?).2 = true →
    ∃ irq : SeLe4n.Irq, st.irqHandlers[irq]? = some n
  /-- The service graph holds no entry. -/
  servicesEmpty : st.services.slotsEmpty

/-- A nonzero registration code is an endpoint's. -/
theorem objTableBackLinks_code_succ {o : Option KernelObject} {m : Nat}
    (h : (objTableBackLinks o).1 = m + 1) :
    ∃ ep, o = some (.endpoint ep) ∧ ep.serviceCode = m + 1 := by
  cases o with
  | none => cases h
  | some o => cases o <;> first | (cases h; done) | exact ⟨_, rfl, h⟩

/-- **An endpoint whose registration code is clear is the target of no
registration.** -/
theorem SystemState.tableReferencesRecorded.notTargeted {st : SystemState}
    (hR : st.tableReferencesRecorded) {e : SeLe4n.ObjId} {ep : Endpoint}
    (hObj : st.objects[e]? = some (.endpoint ep)) (h0 : ep.serviceCode = 0)
    (sid : ServiceId) (reg : ServiceRegistration) (hs : st.serviceRegistry[sid]? = some reg) :
    reg.endpointCap.target ≠ .object e := fun ht => by
  obtain ⟨e', he', hc⟩ := hR.registry sid reg hs
  rw [ht] at he'; cases he'
  rw [hObj] at hc
  simp [KernelObject.tableBackLinks, h0] at hc

/-- **A step that keeps the reference tables and every object's back-links.**
Every kernel step but a registration and a revocation is one: it writes none of
the three tables, and every object it stores holds the back-links of the one it
replaces. -/
def SystemState.TableReferenceFrame (st st' : SystemState) : Prop :=
  st'.referenceTables = st.referenceTables ∧
  ∀ k : SeLe4n.ObjId, objTableBackLinks st'.objects[k]? = objTableBackLinks st.objects[k]?

/-- An in-place object rewrite writes no reference table. -/
@[simp] theorem SystemState.rewriteObject_referenceTables (st : SystemState) (k : SeLe4n.ObjId)
    (obj : KernelObject) (h : st.rewriteAdmissible k obj) :
    (st.rewriteObject k obj h).referenceTables = st.referenceTables := rfl

/-- A thread write writes no reference table. -/
@[simp] theorem SystemState.updateTcb_referenceTables (st : SystemState) (tid : SeLe4n.ThreadId)
    (f : TCB → TCB) : (st.updateTcb tid f).referenceTables = st.referenceTables := by
  unfold SystemState.updateTcb; split <;> rfl

namespace SystemState.TableReferenceFrame

/-- A kind-preserving write that writes no reference table is a frame: it keeps
every object's back-links (`kindPreservingWrite.tableBackLinks`). -/
theorem of_kindPreservingWrite {st st' : SystemState} (hK : kindPreservingWrite st st')
    (hT : st'.referenceTables = st.referenceTables) : TableReferenceFrame st st' :=
  ⟨hT, fun k => by
    rw [objTableBackLinks_eq_map, objTableBackLinks_eq_map, hK.tableBackLinks k]⟩

/-- **A frame keeps the references recorded.** -/
theorem preserves {st st' : SystemState} (h : TableReferenceFrame st st')
    (hR : st.tableReferencesRecorded) : st'.tableReferencesRecorded := by
  obtain ⟨hT, hB⟩ := h
  simp only [referenceTables, Prod.mk.injEq] at hT
  obtain ⟨hReg, hIrq, hSvc⟩ := hT
  exact ⟨hReg ▸ hR.registryInvExtK,
    fun sid reg h => by
      rw [hReg] at h
      obtain ⟨e, he, hc⟩ := hR.registry sid reg h
      exact ⟨e, he, by rw [hB]; exact hc⟩,
    fun e n h => by rw [hB] at h; rw [hReg]; exact hR.serviceCodes e n h,
    fun irq n h => by rw [hIrq] at h; rw [hB]; exact hR.irqHandlers irq n h,
    fun n h => by rw [hB] at h; rw [hIrq]; exact hR.irqBound n h,
    hSvc ▸ hR.servicesEmpty⟩

theorem refl (st : SystemState) : TableReferenceFrame st st := ⟨rfl, fun _ => rfl⟩

theorem trans {st st' st'' : SystemState} (h1 : TableReferenceFrame st st')
    (h2 : TableReferenceFrame st' st'') : TableReferenceFrame st st'' :=
  ⟨h2.1.trans h1.1, fun k => (h2.2 k).trans (h1.2 k)⟩

/-- A step that writes no object and no reference table. -/
theorem of_objects_eq {st st' : SystemState} (hO : st'.objects = st.objects)
    (hT : st'.referenceTables = st.referenceTables) : TableReferenceFrame st st' :=
  ⟨hT, fun k => by rw [hO]⟩

/-- A step writing no reference table whose every slot maps to the back-links of
the slot it replaces, read through `Option.map`. -/
theorem of_map_tableBackLinks {st st' : SystemState}
    (hT : st'.referenceTables = st.referenceTables)
    (h : ∀ k : SeLe4n.ObjId, (st'.objects[k]?).map KernelObject.tableBackLinks =
      (st.objects[k]?).map KernelObject.tableBackLinks) : TableReferenceFrame st st' :=
  ⟨hT, fun k => by rw [objTableBackLinks_eq_map, objTableBackLinks_eq_map, h k]⟩

/-- A step whose every slot maps to the back-links of the slot it replaces. -/
theorem of_getElem {st st' : SystemState} (hT : st'.referenceTables = st.referenceTables)
    (h : ∀ k : SeLe4n.ObjId, objTableBackLinks st'.objects[k]? = objTableBackLinks st.objects[k]?) :
    TableReferenceFrame st st' := ⟨hT, h⟩

/-- **One object written into the store** holding the back-links of the slot it
replaces, the reference tables untouched: the store primitive every object write
is built from. -/
theorem insert {st st' : SystemState} {k : SeLe4n.ObjId} {obj : KernelObject}
    (hInv : st.objects.invExt) (hO : st'.objects = st.objects.insert k obj)
    (hT : st'.referenceTables = st.referenceTables)
    (hB : obj.tableBackLinks = objTableBackLinks st.objects[k]?) : TableReferenceFrame st st' :=
  ⟨hT, fun j => by
    rw [hO]
    by_cases hj : k = j
    · subst hj
      simp only [RHTable_getElem?_eq_get?] at hB ⊢
      rw [RHTable.getElem?_insert_self st.objects _ obj hInv]
      exact hB
    · simp only [RHTable_getElem?_eq_get?]
      rw [RHTable.getElem?_insert_ne st.objects _ _ obj (fun hb => hj (eq_of_beq hb)) hInv]⟩

/-- **Stores that agree up to a view keeping the back-links**: a step whose
every slot maps, under `g`, to what the old slot maps to, where `g` keeps every
object's table back-links (clearing a thread's run-queue or space links, for
instance). -/
theorem of_map {st st' : SystemState} {g : KernelObject → KernelObject}
    (hg : ∀ o, (g o).tableBackLinks = o.tableBackLinks)
    (hT : st'.referenceTables = st.referenceTables)
    (h : ∀ k : SeLe4n.ObjId, (st'.objects[k]?).map g = (st.objects[k]?).map g) :
    TableReferenceFrame st st' :=
  ⟨hT, fun k => by
    have hk := h k
    cases h1 : st'.objects[k]? <;> cases h2 : st.objects[k]? <;>
      simp only [h1, h2, Option.map_some, Option.map_none, Option.some.injEq,
        reduceCtorEq] at hk <;> simp only [objTableBackLinks_some, objTableBackLinks_none]
    rw [← hg, hk, hg]⟩

/-- `storeObject` writes no reference table. -/
theorem _root_.SeLe4n.Model.storeObject_referenceTables {st st' : SystemState} {k : SeLe4n.ObjId}
    {obj : KernelObject} (hS : SeLe4n.Model.storeObject k obj st = .ok ((), st')) :
    st'.referenceTables = st.referenceTables := by
  unfold SeLe4n.Model.storeObject at hS; cases hS; rfl

/-- **The store primitive**: `storeObject` of an object holding the back-links
of the slot it replaces. -/
theorem storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {obj : KernelObject}
    (hInv : st.objects.invExt) (hS : SeLe4n.Model.storeObject k obj st = .ok ((), st'))
    (hB : obj.tableBackLinks = objTableBackLinks st.objects[k]?) : TableReferenceFrame st st' := by
  unfold SeLe4n.Model.storeObject at hS; cases hS
  exact insert hInv rfl rfl hB

/-- **The in-place rewrite primitive**: `rewriteObject` of an object holding the
back-links of the one it replaces. -/
theorem rewriteObject {st : SystemState} {k : SeLe4n.ObjId} {obj : KernelObject}
    (h : st.rewriteAdmissible k obj) (hInv : st.objects.invExt)
    (hB : obj.tableBackLinks = objTableBackLinks st.objects[k]?) :
    TableReferenceFrame st (st.rewriteObject k obj h) :=
  insert hInv rfl rfl hB

/-- A thread holds no table back-link, so a thread written over a thread keeps them. -/
theorem tcb_over {st : SystemState} {k : SeLe4n.ObjId} {t t' : TCB}
    (hO : st.objects[k]? = some (.tcb t)) :
    (KernelObject.tcb t').tableBackLinks = objTableBackLinks st.objects[k]? := by
  rw [hO]; rfl

/-- **The thread write primitive** (`updateTcb`). -/
theorem updateTcb (st : SystemState) (tid : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt) : TableReferenceFrame st (st.updateTcb tid f) := by
  unfold SystemState.updateTcb
  split
  · rename_i t hT _
    exact rewriteObject _ hInv (tcb_over ((getTcb?_eq_some_iff st tid t).mp hT))
  · exact refl st

/-- **The scheduling-context write primitive** (`updateSchedContext`): a context
holds no table back-link. -/
theorem updateSchedContext (st : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SeLe4n.Kernel.SchedContext → SeLe4n.Kernel.SchedContext) (hInv : st.objects.invExt) :
    TableReferenceFrame st (st.updateSchedContext scId f) := by
  unfold SystemState.updateSchedContext
  split
  · rename_i sc hS _
    exact rewriteObject _ hInv (by
      rw [(getSchedContext?_eq_some_iff st scId sc).mp hS]; rfl)
  · exact refl st

/-- A step whose every slot holding no thread reads as it did, both ways, and
which writes no reference table, keeps every object's back-links: a thread
holds none. -/
theorem of_offTcb {st st' : SystemState}
    (hT : st'.referenceTables = st.referenceTables)
    (h : ∀ (k : SeLe4n.ObjId) (o : KernelObject), (∀ t, o ≠ .tcb t) →
      (st'.objects[k]? = some o ↔ st.objects[k]? = some o)) :
    TableReferenceFrame st st' := ⟨hT, fun k => by
  cases h1 : st'.objects[k]? with
  | none =>
    cases h2 : st.objects[k]? with
    | none => rfl
    | some p =>
      cases p with
      | tcb _ => rfl
      | _ =>
        have := (h k _ (fun _ h => KernelObject.noConfusion h)).mpr h2
        rw [h1] at this; cases this
  | some o =>
    cases o with
    | tcb _ =>
      cases h2 : st.objects[k]? with
      | none => rfl
      | some p =>
        cases p with
        | tcb _ => rfl
        | _ =>
          have := (h k _ (fun _ h => KernelObject.noConfusion h)).mpr h2
          rw [h1] at this; cases this
    | _ => rw [(h k _ (fun _ h => KernelObject.noConfusion h)).mp h1]⟩

end SystemState.TableReferenceFrame

/-- **Whether the object at `x` holds no table back-link**: an endpoint no
registration records itself on, a notification no interrupt names; every other
kind, and an empty slot, holds none.  One field of the object, read in place:
what a final delete will ask where it walks the registry, the interrupt table
and the service graph today -- under `tableReferencesRecorded` the two
questions have the same answer (`tableBackLinksClear.namedByNone`). -/
@[inline] def SystemState.tableBackLinksClear (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  match st.getObject? x with
  | some (.endpoint ep) => ep.serviceCode == 0
  | some (.notification n) => !n.irqBound
  | _ => true

theorem SystemState.tableBackLinksClear_iff (st : SystemState) (x : SeLe4n.ObjId) :
    st.tableBackLinksClear x = true ↔ objTableBackLinks st.objects[x]? = (0, false) := by
  unfold tableBackLinksClear getObject?
  cases st.objects[x]? with
  | none => simp
  | some o => cases o <;> simp [KernelObject.tableBackLinks]

/-- **An object whose back-links are clear is named by no table entry**: no
registration holds a capability naming it, no interrupt names it, and the
service graph holds no entry — exactly what the three walks a final delete
still makes establish, now answered by one field of the object. -/
theorem SystemState.tableBackLinksClear.namedByNone {st : SystemState} {x : SeLe4n.ObjId}
    (hR : st.tableReferencesRecorded) (h : st.tableBackLinksClear x = true) :
    (∀ (sid : ServiceId) (reg : ServiceRegistration), st.serviceRegistry[sid]? = some reg →
      ∃ e, reg.endpointCap.target = .object e ∧ e ≠ x) ∧
    (∀ (irq : SeLe4n.Irq) (n : SeLe4n.ObjId), st.irqHandlers[irq]? = some n → n ≠ x) ∧
    (∀ (sid : ServiceId), st.services[sid]? = none) := by
  rw [tableBackLinksClear_iff] at h
  refine ⟨fun sid reg hs => ?_, fun irq n hi hn => ?_, fun sid => ?_⟩
  · obtain ⟨e, he, hc⟩ := hR.registry sid reg hs
    refine ⟨e, he, fun hn => ?_⟩
    subst hn
    rw [h] at hc
    cases hc
  · have hb := hR.irqHandlers irq n hi
    subst hn
    rw [h] at hb
    cases hb
  · exact RHTable.get?_of_slotsEmpty hR.servicesEmpty sid

/-- The empty state records every reference: its tables are empty. -/
theorem SystemState.default_tableReferencesRecorded :
    (default : SystemState).tableReferencesRecorded where
  registryInvExtK := RHTable.empty_invExtK 16 (by omega)
  registry := fun sid reg h => by
    have : (default : SystemState).serviceRegistry[sid]? = none := RHTable_get?_empty 16 (by omega)
    rw [this] at h; cases h
  serviceCodes := fun e n h => by
    have : (default : SystemState).objects[e]? = none := RHTable_get?_empty 16 (by omega)
    rw [this] at h; cases h
  irqHandlers := fun irq n h => by
    have : (default : SystemState).irqHandlers[irq]? = none := RHTable_get?_empty 16 (by omega)
    rw [this] at h; cases h
  irqBound := fun n h => by
    have : (default : SystemState).objects[n]? = none := RHTable_get?_empty 16 (by omega)
    rw [this] at h; cases h
  servicesEmpty := RHTable.empty_slotsEmpty 16 (by omega)

end SeLe4n.Model
