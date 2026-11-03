-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-! # The objects' back-links to the state that names them

Since WS-ZA ZA5.9 the service registry is no table: it is read off the
endpoints (`SystemState.serviceRegistry`), each registration living on the
endpoint it names (`Endpoint.serviceRegistered`, set by `registerService` and
cleared by `revokeService`, with the registration's words beside it,
`Endpoint.service`), so a registration names the endpoint recording it by
construction (`SystemState.serviceRegistry_names` / `serviceRegistry_stored`).
Since WS-ZA ZA5.12 the declassification taint is read off the threads' and
notifications' words (`SystemState.declassificationTaint`).  An interrupt's
notification is named, as in seL4, by the capability in the interrupt's node
slot (`SeLe4n.Kernel.Architecture.irqNodeId`), which the derivation tree and the
finality test see, so no table names an object by id outside every slot.

`tableBackLinksClear` reads an endpoint's own registration record in place of a
walk of the registry (`tableBackLinksClear.namedByNone`), and every step that
leaves every object's back-links as it found them is a `TableReferenceFrame`,
which keeps the registry and the taint. -/

namespace SeLe4n.Model

open SeLe4n.Kernel.RobinHood

/-- The table back-links an object slot holds; an empty slot holds none. -/
@[inline] def objTableBackLinks :
    Option KernelObject → EndpointService × SeLe4n.Kernel.TaintWords
  | some o => o.tableBackLinks
  | none => ({}, {})

@[simp] theorem objTableBackLinks_none : objTableBackLinks none = ({}, {}) := rfl

@[simp] theorem objTableBackLinks_some (o : KernelObject) :
    objTableBackLinks (some o) = o.tableBackLinks := rfl

/-- The back-links of a slot, read off the object the slot maps to. -/
theorem objTableBackLinks_eq_map (o : Option KernelObject) :
    objTableBackLinks o = (o.map KernelObject.tableBackLinks).getD ({}, {}) := by
  cases o <;> rfl

/-- The taint words a slot holds, read as the taint they name: the carved words
(the empty taint) for an empty slot and for every kind but a thread and a
notification. -/
@[inline] def objTaint (o : Option KernelObject) : SeLe4n.Kernel.DeclassificationTaint :=
  (objTableBackLinks o).2.decode

@[simp] theorem objTaint_none : objTaint none = SeLe4n.Kernel.DeclassificationTaint.empty := rfl

/-- **The slot holds taint words**: a thread or a notification is stored there.
Compiled, the lookup's `some` meets this match and is never built
(`RHTable.get?_eq_getByEntry`). -/
@[inline] def objHoldsTaint (o : Option KernelObject) : Bool :=
  match o with
  | some (.tcb _) => true
  | some (.notification _) => true
  | _ => false

theorem objHoldsTaint_some (o : KernelObject) : objHoldsTaint (some o) = o.holdsTaint := by
  cases o <;> rfl

/-- A slot that holds no words reads the empty taint. -/
theorem objTaint_of_not_holds {o : Option KernelObject} (h : objHoldsTaint o = false) :
    objTaint o = SeLe4n.Kernel.DeclassificationTaint.empty := by
  cases o with
  | none => rfl
  | some o =>
    rw [objHoldsTaint_some] at h
    show (o.taintWords).decode = _
    rw [KernelObject.taintWords_of_not_holdsTaint h]; rfl

/-- WS-ZA ZA5.12: **the taint at every id is the taint its object holds in its
words**, empty where no thread or notification is — `SystemState.declassificationTaint`
read through the slot's back-links.  Through WS-ZA ZA5.11 a stored table held
them; the table is gone and the reader reads the words, so it holds of every
state. -/
theorem SystemState.taintStored (st : SystemState) (k : SeLe4n.ObjId) :
    st.declassificationTaint k = objTaint st.objects[k]? := by
  show (st.taintWordsAt k).decode = _
  rw [SystemState.taintWordsAt_eq]
  cases st.objects[k]? <;> rfl

/-- WS-ZA ZA5.12: **a step keeping every object's taint words keeps the taint.** -/
theorem SystemState.declassificationTaint_eq_of_backLinks {st st' : SystemState}
    (h : ∀ k : SeLe4n.ObjId,
      (objTableBackLinks st'.objects[k]?).2 = (objTableBackLinks st.objects[k]?).2) :
    st'.declassificationTaint = st.declassificationTaint :=
  funext fun k => by rw [SystemState.taintStored, SystemState.taintStored, objTaint, objTaint, h]

/-- **The registry's entry under `sid` is the record of the endpoint with that
id, read off its back-link.** -/
theorem SystemState.serviceRegistry_getElem?_backLinks (st : SystemState) (sid : ServiceId) :
    st.serviceRegistry[sid]? =
      if (objTableBackLinks st.objects[SeLe4n.ObjId.ofNat sid.toNat]?).1.registered then
        some ((objTableBackLinks st.objects[SeLe4n.ObjId.ofNat sid.toNat]?).1.registrationAt
          (SeLe4n.ObjId.ofNat sid.toNat))
      else none := by
  rw [SystemState.serviceRegistry_getElem?]
  cases st.objects[SeLe4n.ObjId.ofNat sid.toNat]? with
  | none => rfl
  | some o =>
    cases o with
    | endpoint ep => cases h : ep.serviceRegistered <;> simp [KernelObject.tableBackLinks, h]
    | _ => rfl

/-- **States whose objects hold one set of back-links have one registry**: the
registry is read off the endpoints' back-links. -/
theorem SystemState.serviceRegistry_eq_of_backLinks {st st' : SystemState}
    (h : ∀ k : SeLe4n.ObjId, objTableBackLinks st'.objects[k]? = objTableBackLinks st.objects[k]?) :
    st'.serviceRegistry = st.serviceRegistry :=
  ServiceRegistryView.ext fun sid => by
    rw [SystemState.serviceRegistry_getElem?_backLinks, SystemState.serviceRegistry_getElem?_backLinks,
      h]

/-- **A registration names an endpoint recording it, under that endpoint's
id** — by construction, the registry being read off the endpoints. -/
theorem SystemState.serviceRegistry_names (st : SystemState) {sid : ServiceId}
    {reg : ServiceRegistration} (hs : st.serviceRegistry[sid]? = some reg) :
    ∃ e, reg.endpointCap.target = .object e ∧ sid = ServiceId.ofNat e.toNat ∧
      (objTableBackLinks st.objects[e]?).1.registered = true := by
  rw [SystemState.serviceRegistry_getElem?_backLinks] at hs
  split at hs
  · rename_i hc
    cases hs
    exact ⟨_, rfl, rfl, hc⟩
  · cases hs

/-- **An endpoint's registration flag names the registration its record
holds**, under the endpoint's id. -/
theorem SystemState.serviceRegistry_stored (st : SystemState) (e : SeLe4n.ObjId)
    (h : (objTableBackLinks st.objects[e]?).1.registered = true) :
    st.serviceRegistry[ServiceId.ofNat e.toNat]? =
      some ((objTableBackLinks st.objects[e]?).1.registrationAt e) := by
  rw [SystemState.serviceRegistry_getElem?_backLinks]
  exact if_pos h

/-- **An endpoint's registration flag names a registration of it**, under its
own id. -/
theorem SystemState.serviceRegistry_flag (st : SystemState) (e : SeLe4n.ObjId)
    (h : (objTableBackLinks st.objects[e]?).1.registered = true) :
    ∃ reg, st.serviceRegistry[ServiceId.ofNat e.toNat]? = some reg ∧
      reg.endpointCap.target = .object e :=
  ⟨_, st.serviceRegistry_stored e h, rfl⟩

/-- **The registration under a registered endpoint's id is the one its record
holds.** -/
theorem SystemState.serviceRegistry_of_endpoint (st : SystemState) {e : SeLe4n.ObjId}
    {ep : Endpoint} (hObj : st.objects[e]? = some (.endpoint ep))
    (h : ep.serviceRegistered = true) :
    st.serviceRegistry[ServiceId.ofNat e.toNat]? = some (ep.service.registrationAt e) := by
  rw [SystemState.serviceRegistry_getElem?]
  show (match st.objects[e]? with
    | some (.endpoint ep) => if ep.serviceRegistered then some (ep.service.registrationAt e) else none
    | _ => none) = _
  rw [hObj]; simp [h]

/-- **An endpoint whose registration flag is clear is the target of no
registration.** -/
theorem SystemState.serviceRegistry_notTargeted (st : SystemState) {e : SeLe4n.ObjId}
    {ep : Endpoint} (hObj : st.objects[e]? = some (.endpoint ep)) (h0 : ep.serviceRegistered = false)
    (sid : ServiceId) (reg : ServiceRegistration) (hs : st.serviceRegistry[sid]? = some reg) :
    reg.endpointCap.target ≠ .object e := fun ht => by
  obtain ⟨e', he', -, hc⟩ := st.serviceRegistry_names hs
  rw [ht] at he'; cases he'
  rw [hObj] at hc
  simp [KernelObject.tableBackLinks, h0] at hc

/-- **A step that keeps every object's back-links.**  Every kernel step but a
registration and a revocation is one: every object it stores holds the
back-links of the one it replaces, so it keeps the service registry
(`SystemState.serviceRegistry_eq_of_backLinks`) and the taint. -/
def SystemState.TableReferenceFrame (st st' : SystemState) : Prop :=
  ∀ k : SeLe4n.ObjId, objTableBackLinks st'.objects[k]? = objTableBackLinks st.objects[k]?

/-- WS-ZA ZA5.11: **two stores whose every slot holds the same taint words** —
the part of `TableReferenceFrame`'s back-link clause a thread write owes, since a
thread's taint words are its only back-link. -/
def SameTaintWords (a b : RHTable SeLe4n.ObjId KernelObject) : Prop :=
  ∀ k : SeLe4n.ObjId, (objTableBackLinks b[k]?).2 = (objTableBackLinks a[k]?).2

namespace SameTaintWords

theorem refl (a : RHTable SeLe4n.ObjId KernelObject) : SameTaintWords a a := fun _ => rfl

theorem trans {a b c : RHTable SeLe4n.ObjId KernelObject} (h1 : SameTaintWords a b)
    (h2 : SameTaintWords b c) : SameTaintWords a c := fun k => (h2 k).trans (h1 k)

theorem of_eq {a b : RHTable SeLe4n.ObjId KernelObject} (h : b = a) : SameTaintWords a b :=
  fun _ => by rw [h]

/-- A thread written over a thread with the same taint words. -/
theorem insert_tcb {a : RHTable SeLe4n.ObjId KernelObject} {k : SeLe4n.ObjId} {t t' : TCB}
    (hInv : a.invExt) (hAt : a[k]? = some (.tcb t))
    (hW : t'.taintWords = t.taintWords := by taint_words_kept) :
    SameTaintWords a (a.insert k (.tcb t')) := fun j => by
  by_cases hj : k = j
  · subst hj
    simp only [RHTable_getElem?_eq_get?] at hAt ⊢
    rw [RHTable.getElem?_insert_self a _ _ hInv, hAt]
    simp only [objTableBackLinks_some, KernelObject.tableBackLinks, hW]
  · simp only [RHTable_getElem?_eq_get?]
    rw [RHTable.getElem?_insert_ne a _ _ _ (fun hb => hj (eq_of_beq hb)) hInv]

/-- An object written over one holding the same taint words. -/
theorem insert {a : RHTable SeLe4n.ObjId KernelObject} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : a.invExt) (hW : o.tableBackLinks.2 = (objTableBackLinks a[k]?).2) :
    SameTaintWords a (a.insert k o) := fun j => by
  by_cases hj : k = j
  · subst hj
    simp only [RHTable_getElem?_eq_get?] at hW ⊢
    rw [RHTable.getElem?_insert_self a _ _ hInv]
    exact hW
  · simp only [RHTable_getElem?_eq_get?]
    rw [RHTable.getElem?_insert_ne a _ _ _ (fun hb => hj (eq_of_beq hb)) hInv]

end SameTaintWords

namespace SystemState.TableReferenceFrame

/-- A kind-preserving write is a frame: it keeps every object's back-links
(`kindPreservingWrite.tableBackLinks`). -/
theorem of_kindPreservingWrite {st st' : SystemState} (hK : kindPreservingWrite st st') :
    TableReferenceFrame st st' := fun k => by
  rw [objTableBackLinks_eq_map, objTableBackLinks_eq_map, hK.tableBackLinks k]

/-- WS-ZA ZA5.12: **a frame keeps the taint**: the taint is read off the
objects' words, which are back-links a frame keeps. -/
theorem declassificationTaint {st st' : SystemState} (h : TableReferenceFrame st st') :
    st'.declassificationTaint = st.declassificationTaint :=
  SystemState.declassificationTaint_eq_of_backLinks fun k => by rw [h]

/-- **A frame keeps the service registry**: the registry is read off the
endpoints' back-links, which a frame keeps. -/
theorem serviceRegistry {st st' : SystemState} (h : TableReferenceFrame st st') :
    st'.serviceRegistry = st.serviceRegistry :=
  SystemState.serviceRegistry_eq_of_backLinks h

theorem refl (st : SystemState) : TableReferenceFrame st st := fun _ => rfl

theorem trans {st st' st'' : SystemState} (h1 : TableReferenceFrame st st')
    (h2 : TableReferenceFrame st' st'') : TableReferenceFrame st st'' :=
  fun k => (h2 k).trans (h1 k)

/-- A step that writes no object. -/
theorem of_objects_eq {st st' : SystemState} (hO : st'.objects = st.objects) :
    TableReferenceFrame st st' :=
  fun k => by rw [hO]

/-- A step whose every slot maps to the back-links of the slot it replaces, read
through `Option.map`. -/
theorem of_map_tableBackLinks {st st' : SystemState}
    (h : ∀ k : SeLe4n.ObjId, (st'.objects[k]?).map KernelObject.tableBackLinks =
      (st.objects[k]?).map KernelObject.tableBackLinks) : TableReferenceFrame st st' :=
  fun k => by rw [objTableBackLinks_eq_map, objTableBackLinks_eq_map, h k]

/-- A step whose every slot maps to the back-links of the slot it replaces. -/
theorem of_getElem {st st' : SystemState}
    (h : ∀ k : SeLe4n.ObjId, objTableBackLinks st'.objects[k]? = objTableBackLinks st.objects[k]?) :
    TableReferenceFrame st st' := h

/-- **One object written into the store** holding the back-links of the slot it
replaces: the store primitive every object write is built from. -/
theorem insert {st st' : SystemState} {k : SeLe4n.ObjId} {obj : KernelObject}
    (hInv : st.objects.invExt) (hO : st'.objects = st.objects.insert k obj)
    (hB : obj.tableBackLinks = objTableBackLinks st.objects[k]?) : TableReferenceFrame st st' :=
  fun j => by
    rw [hO]
    by_cases hj : k = j
    · subst hj
      simp only [RHTable_getElem?_eq_get?] at hB ⊢
      rw [RHTable.getElem?_insert_self st.objects _ obj hInv]
      exact hB
    · simp only [RHTable_getElem?_eq_get?]
      rw [RHTable.getElem?_insert_ne st.objects _ _ obj (fun hb => hj (eq_of_beq hb)) hInv]

/-- **Stores that agree up to a view keeping the back-links**: a step whose
every slot maps, under `g`, to what the old slot maps to, where `g` keeps every
object's table back-links (clearing a thread's run-queue or space links, for
instance). -/
theorem of_map {st st' : SystemState} {g : KernelObject → KernelObject}
    (hg : ∀ o, (g o).tableBackLinks = o.tableBackLinks)
    (h : ∀ k : SeLe4n.ObjId, (st'.objects[k]?).map g = (st.objects[k]?).map g) :
    TableReferenceFrame st st' :=
  fun k => by
    have hk := h k
    cases h1 : st'.objects[k]? <;> cases h2 : st.objects[k]? <;>
      simp only [h1, h2, Option.map_some, Option.map_none, Option.some.injEq,
        reduceCtorEq] at hk <;> simp only [objTableBackLinks_some, objTableBackLinks_none]
    rw [← hg, hk, hg]

/-- **The store primitive**: `storeObject` of an object holding the back-links
of the slot it replaces. -/
theorem storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {obj : KernelObject}
    (hInv : st.objects.invExt) (hS : SeLe4n.Model.storeObject k obj st = .ok ((), st'))
    (hB : obj.tableBackLinks = objTableBackLinks st.objects[k]?) : TableReferenceFrame st st' := by
  unfold SeLe4n.Model.storeObject at hS; cases hS
  exact insert hInv rfl hB

/-- **The in-place rewrite primitive**: `rewriteObject` of an object holding the
back-links of the one it replaces. -/
theorem rewriteObject {st : SystemState} {k : SeLe4n.ObjId} {obj : KernelObject}
    (h : st.rewriteAdmissible k obj) (hInv : st.objects.invExt)
    (hB : obj.tableBackLinks = objTableBackLinks st.objects[k]?) :
    TableReferenceFrame st (st.rewriteObject k obj h) :=
  insert hInv rfl hB

/-- A thread's only table back-link is its taint words (WS-ZA ZA5.11), so a
thread written over a thread keeping them keeps its back-links. -/
theorem tcb_over {st : SystemState} {k : SeLe4n.ObjId} {t t' : TCB}
    (hO : st.objects[k]? = some (.tcb t))
    (hW : t'.taintWords = t.taintWords := by taint_words_kept) :
    (KernelObject.tcb t').tableBackLinks = objTableBackLinks st.objects[k]? := by
  rw [hO]; simp only [objTableBackLinks_some, KernelObject.tableBackLinks, hW]

/-- **The thread write primitive** (`updateTcb`). -/
theorem updateTcb (st : SystemState) (tid : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt)
    (hW : ∀ t, (f t).taintWords = t.taintWords := by taint_words_kept) :
    TableReferenceFrame st (st.updateTcb tid f) := by
  unfold SystemState.updateTcb
  split
  · rename_i t hT _
    exact rewriteObject _ hInv (tcb_over ((getTcb?_eq_some_iff st tid t).mp hT) (hW t))
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

/-- A step whose every slot holding no thread reads as it did, both ways, which
keeps every slot's taint words, keeps every object's back-links: a thread's
only one is its taint words. -/
theorem of_offTcb {st st' : SystemState}
    (h : ∀ (k : SeLe4n.ObjId) (o : KernelObject), (∀ t, o ≠ .tcb t) →
      (st'.objects[k]? = some o ↔ st.objects[k]? = some o))
    (hW : SameTaintWords st.objects st'.objects) :
    TableReferenceFrame st st' := fun k => by
  have hk := hW k
  cases h1 : st'.objects[k]? with
  | none =>
    cases h2 : st.objects[k]? with
    | none => rfl
    | some p =>
      cases p with
      | tcb _ =>
        rw [h1, h2] at hk
        simp only [objTableBackLinks_some, objTableBackLinks_none, KernelObject.tableBackLinks]
          at hk ⊢
        rw [hk]
      | _ =>
        have := (h k _ (fun _ h => KernelObject.noConfusion h)).mpr h2
        rw [h1] at this; cases this
  | some o =>
    cases o with
    | tcb _ =>
      cases h2 : st.objects[k]? with
      | none =>
        rw [h1, h2] at hk
        simp only [objTableBackLinks_some, objTableBackLinks_none, KernelObject.tableBackLinks]
          at hk ⊢
        rw [hk]
      | some p =>
        cases p with
        | tcb _ =>
          rw [h1, h2] at hk
          simp only [objTableBackLinks_some, KernelObject.tableBackLinks] at hk ⊢
          rw [hk]
        | _ =>
          have := (h k _ (fun _ h => KernelObject.noConfusion h)).mpr h2
          rw [h1] at this; cases this
    | _ => rw [(h k _ (fun _ h => KernelObject.noConfusion h)).mp h1]

end SystemState.TableReferenceFrame

/-- **Whether the object at `x` holds no table back-link**: an endpoint no
registration records itself on; every other kind, and an empty slot, holds
none.  One field of the object, read in place: what a final delete asks in
place of walking the registry (`tableBackLinksClear.namedByNone`). -/
@[inline] def SystemState.tableBackLinksClear (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  match st.getObject? x with
  | some (.endpoint ep) => !ep.serviceRegistered
  | _ => true

theorem SystemState.tableBackLinksClear_iff (st : SystemState) (x : SeLe4n.ObjId) :
    st.tableBackLinksClear x = true ↔
      (objTableBackLinks st.objects[x]?).1 = ({} : EndpointService) := by
  unfold tableBackLinksClear getObject?
  cases st.objects[x]? with
  | none => simp
  | some o =>
    cases o with
    | endpoint ep =>
      cases h : ep.serviceRegistered
      · simp [KernelObject.tableBackLinks, h]
      · simp only [KernelObject.tableBackLinks, h, objTableBackLinks_some, Bool.not_true,
          Bool.false_eq_true, false_iff, if_true]
        intro hc
        have := congrArg (fun p : EndpointService => p.registered) hc
        simp [h] at this
    | _ => simp [KernelObject.tableBackLinks]

/-- **An object whose back-links are clear is named by no registration**: no
registration holds a capability naming it — what a walk of the registry would
establish, answered by one field of the object. -/
theorem SystemState.tableBackLinksClear.namedByNone {st : SystemState} {x : SeLe4n.ObjId}
    (h : st.tableBackLinksClear x = true) :
    ∀ (sid : ServiceId) (reg : ServiceRegistration), st.serviceRegistry[sid]? = some reg →
      ∃ e, reg.endpointCap.target = .object e ∧ e ≠ x := by
  rw [tableBackLinksClear_iff] at h
  intro sid reg hs
  obtain ⟨e, he, -, hc⟩ := st.serviceRegistry_names hs
  refine ⟨e, he, fun hn => ?_⟩
  subst hn
  rw [h] at hc
  cases hc

end SeLe4n.Model
