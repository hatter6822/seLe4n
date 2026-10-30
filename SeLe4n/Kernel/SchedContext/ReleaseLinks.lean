-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Kernel.RobinHood.Invariant.MapValueAt
import SeLe4n.Kernel.SchedContext.ReleaseChain
import SeLe4n.Kernel.SchedContext.Budget

/-!
# The release queue's links in the scheduling contexts (WS-ZA ZA6.3)

As in seL4-MCS, whose release queue links through the threads, a queued
scheduling context's release-queue link lives in the context
(`SchedContext.releaseNextCode`) beside the core whose queue holds it
(`SchedContext.releaseCoreCode`) and the time it is released
(`SchedContext.releaseAt`), and each core keeps only the head and the count
(`SchedulerState.releaseHeadOnCore`, `releaseCountOnCore`).  The scheduler also
carries each core's queue as a whole (`SchedulerState.replenishQueueOnCore`), as
ghost state, the value every scheduler statement reads;
`SystemState.releaseQueueRefined` is the invariant that the two agree.

The kernel reads and writes the queue through the contexts alone: an insert
walks to its sorted place and splices the context in, a removal walks to the
predecessor and splices it out, and the drain detaches the due prefix and moves
the head.  Each writes the ghost queue with the edit the abstract queue makes,
so every statement over the queue reads as before.
-/

namespace SeLe4n.Kernel

/-- A context taken off its release queue: marked on no core.  Its successor
code is kept: every reader masks it by the core code
(`SchedContext.releaseLinkOn`), and the drain walks the detached prefix along
it. -/
@[inline] def SchedContext.leaveRelease (sc : SchedContext) : SchedContext :=
  { sc with releaseCoreCode := 0 }

/-- A context placed on core `c`'s release queue before code `n`, released at
`t`. -/
@[inline] def SchedContext.joinRelease (c : Concurrency.CoreId) (n t : Nat)
    (sc : SchedContext) : SchedContext :=
  { sc with releaseCoreCode := c.val + 1, releaseNextCode := n, releaseAt := t }

/-- A queued context's successor replaced. -/
@[inline] def SchedContext.withReleaseNext (n : Nat) (sc : SchedContext) : SchedContext :=
  { sc with releaseNextCode := n }

/-- The release link a context holds on core `c`: its successor's code and its
release time while it is on `c`'s queue. -/
def SchedContext.releaseLinkOn (sc : SchedContext) (c : Concurrency.CoreId) : Option (Nat × Nat) :=
  if sc.releaseCoreCode = c.val + 1 then some (sc.releaseNextCode, sc.releaseAt) else none

end SeLe4n.Kernel

namespace SeLe4n.Model.SystemState

open SeLe4n.Kernel
open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.ReleaseChain
open SeLe4n.Kernel.Concurrency (CoreId)

/-- WS-ZA ZA6.3: rewrite context `s` through `g` **in its slot**
(`RHTable.mapValueAt`): no probe, no resize, no key moved, so the frame holds
on every object table.  The release queue's link writes go through it; a key
holding no context is left as it is. -/
@[inline] def mapSchedContextInPlace (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) : SystemState :=
  { st with objects := st.objects.mapValueAt s.toObjId (mapSchedContextObject g) }

theorem objects_mapSchedContextInPlace (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) (x : SeLe4n.ObjId) :
    (st.mapSchedContextInPlace s g).objects[x]? =
      if s.toObjId == x then (st.objects[x]?).map (mapSchedContextObject g)
      else st.objects[x]? := by
  simp only [mapSchedContextInPlace, RHTable_getElem?_eq_get?]
  exact RHTable.get?_mapValueAt _ _ _ _

@[simp] theorem mapSchedContextInPlace_scheduler (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) : (st.mapSchedContextInPlace s g).scheduler = st.scheduler := rfl

@[simp] theorem mapSchedContextInPlace_machine (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) : (st.mapSchedContextInPlace s g).machine = st.machine := rfl

theorem mapSchedContextInPlace_getSchedContext?_self (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) :
    (st.mapSchedContextInPlace s g).getSchedContext? s = (st.getSchedContext? s).map g := by
  unfold getSchedContext?
  rw [objects_mapSchedContextInPlace, if_pos (beq_self_eq_true _)]
  cases st.objects[s.toObjId]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem mapSchedContextInPlace_getSchedContext?_ne (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) {y : SeLe4n.SchedContextId} (hy : y ≠ s) :
    (st.mapSchedContextInPlace s g).getSchedContext? y = st.getSchedContext? y := by
  unfold getSchedContext?
  rw [objects_mapSchedContextInPlace, if_neg (by
    simpa using fun e => hy (SeLe4n.SchedContextId.toObjId_injective _ _ e).symm)]

/-- The in-place context write leaves every non-context object where it is. -/
theorem mapSchedContextInPlace_getElem?_of_not_sc (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) (x : SeLe4n.ObjId)
    (h : ∀ sc, st.objects[x]? ≠ some (.schedContext sc)) :
    (st.mapSchedContextInPlace s g).objects[x]? = st.objects[x]? := by
  rw [objects_mapSchedContextInPlace]
  by_cases hk : (s.toObjId == x) = true
  · rw [if_pos hk]
    cases e : st.objects[x]? with
    | none => rfl
    | some o =>
      cases o with
      | schedContext sc => exact absurd e (h sc)
      | _ => rfl
  · rw [if_neg hk]

theorem mapSchedContextInPlace_getTcb? (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) (t : SeLe4n.ThreadId) :
    (st.mapSchedContextInPlace s g).getTcb? t = st.getTcb? t := by
  unfold getTcb?
  rw [objects_mapSchedContextInPlace]
  by_cases hk : (s.toObjId == t.toObjId) = true
  · rw [if_pos hk]
    cases st.objects[t.toObjId]? with
    | none => rfl
    | some o => cases o <;> rfl
  · rw [if_neg hk]

theorem mapSchedContextInPlace_objects_invExt (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) (hInv : st.objects.invExt) :
    (st.mapSchedContextInPlace s g).objects.invExt :=
  RHTable.mapValueAt_invExt _ _ _ hInv

/-! ## Writes to the release fields alone -/

/-- A context with its release-queue fields cleared: what every reader other
than the release queue's sees. -/
def _root_.SeLe4n.Kernel.SchedContext.withoutRelease (sc : SchedContext) : SchedContext :=
  { sc with releaseNextCode := 0, releaseCoreCode := 0, releaseAt := 0 }

/-- An object with a context's release-queue fields cleared. -/
def _root_.SeLe4n.Model.KernelObject.withoutRelease : KernelObject → KernelObject
  | .schedContext sc => .schedContext sc.withoutRelease
  | o => o

@[simp] theorem _root_.SeLe4n.Kernel.SchedContext.withoutRelease_leaveRelease (sc : SchedContext) :
    sc.leaveRelease.withoutRelease = sc.withoutRelease := rfl
@[simp] theorem _root_.SeLe4n.Kernel.SchedContext.withoutRelease_joinRelease (sc : SchedContext)
    (c : CoreId) (n t : Nat) : (sc.joinRelease c n t).withoutRelease = sc.withoutRelease := rfl
@[simp] theorem _root_.SeLe4n.Kernel.SchedContext.withoutRelease_withReleaseNext (sc : SchedContext)
    (n : Nat) : (sc.withReleaseNext n).withoutRelease = sc.withoutRelease := rfl

/-- The release fields hold no refill: a context reads the same refills with
them cleared. -/
@[simp] theorem _root_.SeLe4n.Kernel.SchedContext.replenishments_withoutRelease (sc : SchedContext) :
    sc.withoutRelease.replenishments = sc.replenishments := rfl

/-- Two contexts agreeing off their release-queue fields read the same through
every reading of the rest. -/
theorem _root_.SeLe4n.Kernel.SchedContext.proj_eq_of_withoutRelease_eq {α : Sort _}
    {sc sc' : SchedContext} (f : SchedContext → α) (h : sc'.withoutRelease = sc.withoutRelease)
    (hf : ∀ u : SchedContext, f u.withoutRelease = f u := by intro; rfl) : f sc' = f sc := by
  rw [← hf sc', h, hf]

/-- Two lookups agreeing off the release-queue fields: a context one finds, the
other finds agreeing off those fields. -/
theorem _root_.SeLe4n.Kernel.SchedContext.map_withoutRelease_some {a b : Option SchedContext}
    {sc : SchedContext} (h : a.map SchedContext.withoutRelease = b.map SchedContext.withoutRelease)
    (hb : b = some sc) : ∃ sc', a = some sc' ∧ sc'.withoutRelease = sc.withoutRelease := by
  subst hb
  cases a with
  | none => cases h
  | some sc' => exact ⟨sc', rfl, Option.some.inj h⟩

/-- WS-ZA ZA6.3: `st'` holds `st`'s objects up to the contexts' release-queue
fields: the frame every release-queue edit keeps. -/
def objectsAgreeOffReleaseLinks (st' st : SystemState) : Prop :=
  ∀ x : SeLe4n.ObjId,
    (st'.objects[x]?).map KernelObject.withoutRelease = (st.objects[x]?).map KernelObject.withoutRelease

namespace objectsAgreeOffReleaseLinks

theorem refl (st : SystemState) : objectsAgreeOffReleaseLinks st st := fun _ => rfl

theorem trans {a b d : SystemState} (h₁ : objectsAgreeOffReleaseLinks a b)
    (h₂ : objectsAgreeOffReleaseLinks b d) : objectsAgreeOffReleaseLinks a d :=
  fun x => (h₁ x).trans (h₂ x)

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    objectsAgreeOffReleaseLinks st' st := fun x => by rw [h]

/-- The relation reads the object stores alone. -/
theorem congr {a a' b : SystemState} (ha : a'.objects = a.objects)
    (h : objectsAgreeOffReleaseLinks a b) : objectsAgreeOffReleaseLinks a' b :=
  fun x => by rw [ha]; exact h x

theorem withScheduler {st st' : SystemState} (h : objectsAgreeOffReleaseLinks st' st)
    (sch : SchedulerState) : objectsAgreeOffReleaseLinks { st' with scheduler := sch } st := h

theorem symm {st st' : SystemState} (h : objectsAgreeOffReleaseLinks st' st) :
    objectsAgreeOffReleaseLinks st st' := fun x => (h x).symm

/-- One object written at the same key into two agreeing stores. -/
theorem insert {a b : SystemState} (h : objectsAgreeOffReleaseLinks a b)
    (ha : a.objects.invExt) (hb : b.objects.invExt) (k : SeLe4n.ObjId) (v : KernelObject) :
    objectsAgreeOffReleaseLinks { a with objects := a.objects.insert k v }
      { b with objects := b.objects.insert k v } := fun x => by
  show ((a.objects.insert k v).get? x).map _ = ((b.objects.insert k v).get? x).map _
  rw [RHTable_getElem?_insert _ _ _ ha, RHTable_getElem?_insert _ _ _ hb]
  split
  · rfl
  · exact h x

/-- A TCB rewritten through `f` in two agreeing stores. -/
theorem updateTcb {a b : SystemState} (h : objectsAgreeOffReleaseLinks a b)
    (ha : a.objects.invExt) (hb : b.objects.invExt) (tid : SeLe4n.ThreadId) (f : TCB → TCB) :
    objectsAgreeOffReleaseLinks (a.updateTcb tid f) (b.updateTcb tid f) := by
  have hGet : a.getTcb? tid = b.getTcb? tid := by
    unfold SystemState.getTcb?
    have hx := h tid.toObjId
    cases e : b.objects[tid.toObjId]? with
    | none =>
      rw [e] at hx
      cases e' : a.objects[tid.toObjId]? with
      | none => rfl
      | some _ => rw [e'] at hx; cases hx
    | some o =>
      rw [e] at hx
      cases e' : a.objects[tid.toObjId]? with
      | none => rw [e'] at hx; cases hx
      | some o' =>
        rw [e'] at hx
        simp only [Option.map_some, Option.some.injEq] at hx
        cases o <;> cases o' <;> simp_all [KernelObject.withoutRelease]
  cases hA : a.getTcb? tid with
  | none =>
    rw [SystemState.updateTcb_eq_self_of_none hA, SystemState.updateTcb_eq_self_of_none (hGet ▸ hA)]
    exact h
  | some t =>
    rw [SystemState.updateTcb_eq_of_some hA, SystemState.updateTcb_eq_of_some (hGet ▸ hA)]
    exact h.insert ha hb _ _

/-- An in-place context write that changes only the release fields. -/
theorem mapSchedContextInPlace (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) (hg : ∀ sc, (g sc).withoutRelease = sc.withoutRelease) :
    objectsAgreeOffReleaseLinks (st.mapSchedContextInPlace s g) st := by
  intro x
  rw [objects_mapSchedContextInPlace]
  split
  · cases st.objects[x]? with
    | none => rfl
    | some o =>
      cases o <;> simp only [Option.map_some, mapSchedContextObject, KernelObject.withoutRelease, hg]
  · rfl

variable {st st' : SystemState} (h : objectsAgreeOffReleaseLinks st' st)
include h

/-- A non-context object is the same object in both stores. -/
theorem get_of_not_sc {x : SeLe4n.ObjId} {o : KernelObject} (hNot : ∀ sc, o ≠ .schedContext sc)
    (hx : st.objects[x]? = some o) : st'.objects[x]? = some o := by
  have hx' := h x
  rw [hx] at hx'
  cases e : st'.objects[x]? with
  | none => rw [e] at hx'; cases hx'
  | some o' =>
    rw [e] at hx'
    simp only [Option.map_some, Option.some.injEq] at hx'
    cases o with
    | schedContext sc => exact absurd rfl (hNot sc)
    | _ => cases o' <;> first | (simp only [KernelObject.withoutRelease] at hx'; rw [hx']) | cases hx'

theorem getTcb? (t : SeLe4n.ThreadId) : st'.getTcb? t = st.getTcb? t := by
  unfold SystemState.getTcb?
  have hx := h t.toObjId
  cases e : st.objects[t.toObjId]? with
  | none =>
    rw [e] at hx
    cases e' : st'.objects[t.toObjId]? with
    | none => rfl
    | some _ => rw [e'] at hx; cases hx
  | some o =>
    cases o with
    | tcb tc => rw [h.get_of_not_sc (fun _ e => KernelObject.noConfusion e) e]
    | schedContext sc =>
      rw [e] at hx
      cases e' : st'.objects[t.toObjId]? with
      | none => simp [e'] at hx
      | some o' => rw [e'] at hx; cases o' <;> first | rfl | cases hx
    | _ => rw [h.get_of_not_sc (fun _ e => KernelObject.noConfusion e) e]

theorem getSchedContext? (s : SeLe4n.SchedContextId) :
    (st'.getSchedContext? s).map SchedContext.withoutRelease =
      (st.getSchedContext? s).map SchedContext.withoutRelease := by
  unfold SystemState.getSchedContext?
  have hx := h s.toObjId
  cases e : st.objects[s.toObjId]? with
  | none =>
    rw [e] at hx
    cases e' : st'.objects[s.toObjId]? with
    | none => rfl
    | some _ => rw [e'] at hx; cases hx
  | some o =>
    rw [e] at hx
    cases e' : st'.objects[s.toObjId]? with
    | none => rw [e'] at hx; cases hx
    | some o' =>
      rw [e'] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      cases o <;> cases o' <;> simp_all [KernelObject.withoutRelease]

/-- No release field is a back-link, so every slot keeps its back-links. -/
theorem tableBackLinks (k : SeLe4n.ObjId) :
    (st'.objects[k]?).map KernelObject.tableBackLinks =
      (st.objects[k]?).map KernelObject.tableBackLinks := by
  have e : ∀ o : KernelObject, o.withoutRelease.tableBackLinks = o.tableBackLinks := by
    intro o; cases o <;> rfl
  have hx := congrArg (Option.map KernelObject.tableBackLinks) (h k)
  simpa only [Option.map_map, Function.comp_def, e] using hx

/-- Every reading of a context off its release-queue fields is the same. -/
theorem getSchedContext?_map {α : Type _} (f : SchedContext → α)
    (hf : ∀ sc, f sc.withoutRelease = f sc := by intro; rfl) (s : SeLe4n.SchedContextId) :
    (st'.getSchedContext? s).map f = (st.getSchedContext? s).map f := by
  have e := congrArg (Option.map f) (h.getSchedContext? s)
  simpa only [Option.map_map, Function.comp_def, hf] using e

/-- A context resolving in `st'` resolves in `st` agreeing off its release-queue
fields. -/
theorem getSchedContext?_some' {s : SeLe4n.SchedContextId} {sc' : SchedContext}
    (hs : st'.getSchedContext? s = some sc') :
    ∃ sc, st.getSchedContext? s = some sc ∧ sc'.withoutRelease = sc.withoutRelease := by
  have e := h.getSchedContext? s
  rw [hs] at e
  cases e' : st.getSchedContext? s with
  | none => rw [e'] at e; cases e
  | some sc => rw [e'] at e; exact ⟨sc, rfl, Option.some.inj e⟩

/-- ...and from `st` to `st'`. -/
theorem getSchedContext?_some {s : SeLe4n.SchedContextId} {sc : SchedContext}
    (hs : st.getSchedContext? s = some sc) :
    ∃ sc', st'.getSchedContext? s = some sc' ∧ sc'.withoutRelease = sc.withoutRelease := by
  have e := h.getSchedContext? s
  rw [hs] at e
  cases e' : st'.getSchedContext? s with
  | none => rw [e'] at e; cases e
  | some sc' => rw [e'] at e; exact ⟨sc', rfl, Option.some.inj e⟩

theorem getSchedContext?_isSome (s : SeLe4n.SchedContextId) :
    (st'.getSchedContext? s).isSome = (st.getSchedContext? s).isSome := by
  have := congrArg Option.isSome (h.getSchedContext? s)
  simpa using this

/-- Each slot reads the same in both stores, or holds a context in both that
agree off the release fields. -/
theorem pointwise (x : SeLe4n.ObjId) :
    st'.objects[x]? = st.objects[x]? ∨
      ∃ sc sc' : SchedContext, st.objects[x]? = some (.schedContext sc) ∧
        st'.objects[x]? = some (.schedContext sc') ∧ sc'.withoutRelease = sc.withoutRelease := by
  have hx := h x
  cases e : st.objects[x]? with
  | none =>
    rw [e] at hx
    cases e' : st'.objects[x]? with
    | none => exact Or.inl rfl
    | some _ => rw [e'] at hx; cases hx
  | some o =>
    cases o with
    | schedContext sc =>
      rw [e] at hx
      cases e' : st'.objects[x]? with
      | none => rw [e'] at hx; cases hx
      | some o' =>
        rw [e'] at hx
        simp only [Option.map_some, Option.some.injEq] at hx
        cases o' <;> simp only [KernelObject.withoutRelease, reduceCtorEq] at hx
        rename_i sc'
        exact Or.inr ⟨sc, sc', rfl, rfl, KernelObject.schedContext.inj hx⟩
    | _ => exact Or.inl (h.get_of_not_sc (fun _ e => KernelObject.noConfusion e) e)

theorem replenishments (s : SeLe4n.SchedContextId) :
    (st'.getSchedContext? s).map SchedContext.replenishments =
      (st.getSchedContext? s).map SchedContext.replenishments := by
  have := congrArg (Option.map SchedContext.replenishments) (h.getSchedContext? s)
  simpa [Option.map_map, Function.comp_def] using this

end objectsAgreeOffReleaseLinks

/-! ## Reading the queue through the contexts -/

/-- WS-ZA ZA6.3: context `s`'s release link on core `c`, read from the context:
its successor's code and release time while it is on `c`'s queue, none when it
is on another core's, on none, or is no context. -/
def releaseLinkOn (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    Option (Nat × Nat) :=
  match st.getSchedContext? s with
  | some sc => sc.releaseLinkOn c
  | none => none

/-- `s`'s successor code on core `c`'s queue (`0` off it), read as one field. -/
@[inline] def releaseNextOn (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) : Nat :=
  match st.getSchedContext? s with
  | some sc => if sc.releaseCoreCode = c.val + 1 then sc.releaseNextCode else 0
  | none => 0

/-- `s`'s release time on core `c`'s queue (`0` off it), read as one field. -/
@[inline] def releaseAtOn (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) : Nat :=
  match st.getSchedContext? s with
  | some sc => if sc.releaseCoreCode = c.val + 1 then sc.releaseAt else 0
  | none => 0

/-- Is `s` on core `c`'s release queue?  Read from the context alone. -/
@[inline] def releaseQueuedOn (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) : Bool :=
  match st.getSchedContext? s with
  | some sc => sc.releaseCoreCode == c.val + 1
  | none => false

theorem releaseNextOn_eq (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    st.releaseNextOn c s = match st.releaseLinkOn c s with | some (n, _) => n | none => 0 := by
  unfold releaseNextOn releaseLinkOn SchedContext.releaseLinkOn
  cases st.getSchedContext? s with
  | none => rfl
  | some sc => by_cases h : sc.releaseCoreCode = c.val + 1 <;> simp [h]

theorem releaseAtOn_eq (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    st.releaseAtOn c s = match st.releaseLinkOn c s with | some (_, t) => t | none => 0 := by
  unfold releaseAtOn releaseLinkOn SchedContext.releaseLinkOn
  cases st.getSchedContext? s with
  | none => rfl
  | some sc => by_cases h : sc.releaseCoreCode = c.val + 1 <;> simp [h]

theorem releaseQueuedOn_eq (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    st.releaseQueuedOn c s = (st.releaseLinkOn c s).isSome := by
  unfold releaseQueuedOn releaseLinkOn SchedContext.releaseLinkOn
  cases st.getSchedContext? s with
  | none => rfl
  | some sc => by_cases h : sc.releaseCoreCode = c.val + 1 <;> simp [h]

theorem releaseLinkOn_of_getSchedContext? {st st' : SystemState} {s : SeLe4n.SchedContextId}
    (h : st'.getSchedContext? s = st.getSchedContext? s) (c : CoreId) :
    st'.releaseLinkOn c s = st.releaseLinkOn c s := by
  unfold releaseLinkOn; rw [h]

/-- Two states hold the same release links: every context's link on every core
reads alike. -/
def ReleaseLinksAgree (st' st : SystemState) : Prop :=
  ∀ c s, st'.releaseLinkOn c s = st.releaseLinkOn c s

namespace ReleaseLinksAgree

theorem refl (st : SystemState) : ReleaseLinksAgree st st := fun _ _ => rfl

theorem trans {a b d : SystemState} (h₁ : ReleaseLinksAgree a b) (h₂ : ReleaseLinksAgree b d) :
    ReleaseLinksAgree a d := fun c s => (h₁ c s).trans (h₂ c s)

theorem of_getSchedContext? {st st' : SystemState}
    (h : ∀ s, st'.getSchedContext? s = st.getSchedContext? s) : ReleaseLinksAgree st' st :=
  fun c s => releaseLinkOn_of_getSchedContext? (h s) c

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    ReleaseLinksAgree st' st :=
  of_getSchedContext? fun s => by unfold getSchedContext?; rw [h]

theorem nextOn {st st' : SystemState} (h : ReleaseLinksAgree st' st) (c : CoreId) :
    st'.releaseNextOn c = st.releaseNextOn c :=
  funext fun s => by rw [releaseNextOn_eq, releaseNextOn_eq, h c s]

theorem atOn {st st' : SystemState} (h : ReleaseLinksAgree st' st) (c : CoreId) :
    st'.releaseAtOn c = st.releaseAtOn c :=
  funext fun s => by rw [releaseAtOn_eq, releaseAtOn_eq, h c s]

theorem queuedOn {st st' : SystemState} (h : ReleaseLinksAgree st' st) (c : CoreId) :
    st'.releaseQueuedOn c = st.releaseQueuedOn c :=
  funext fun s => by rw [releaseQueuedOn_eq, releaseQueuedOn_eq, h c s]

end ReleaseLinksAgree

/-- A context write that keeps the three release fields keeps every release link. -/
theorem ReleaseLinksAgree.mapSchedContextInPlace (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext)
    (hg : ∀ sc, (g sc).releaseCoreCode = sc.releaseCoreCode ∧
      (g sc).releaseNextCode = sc.releaseNextCode ∧ (g sc).releaseAt = sc.releaseAt) :
    ReleaseLinksAgree (st.mapSchedContextInPlace s g) st := by
  intro c y
  by_cases hy : y = s
  · subst hy
    unfold releaseLinkOn
    rw [mapSchedContextInPlace_getSchedContext?_self]
    cases st.getSchedContext? y with
    | none => rfl
    | some sc =>
      obtain ⟨h1, h2, h3⟩ := hg sc
      simp only [Option.map_some, SchedContext.releaseLinkOn, h1, h2, h3]
  · exact releaseLinkOn_of_getSchedContext? (mapSchedContextInPlace_getSchedContext?_ne _ _ _ hy) c

/-- An object's release link on core `c`: a context's, none for any other
object or an empty slot. -/
def objReleaseLinkOn : Option KernelObject → CoreId → Option (Nat × Nat)
  | some (.schedContext sc), c => sc.releaseLinkOn c
  | _, _ => none

theorem releaseLinkOn_eq_obj (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    st.releaseLinkOn c s = objReleaseLinkOn st.objects[s.toObjId]? c := by
  unfold releaseLinkOn getSchedContext?
  rcases st.objects[s.toObjId]? with _ | o
  · rfl
  · cases o <;> rfl

/-- Two stores whose every slot gives the same release links hold the same
release links. -/
theorem ReleaseLinksAgree.of_objReleaseLinkOn {st st' : SystemState}
    (h : ∀ (k : SeLe4n.ObjId) c, objReleaseLinkOn st'.objects[k]? c = objReleaseLinkOn st.objects[k]? c) :
    ReleaseLinksAgree st' st := fun c s => by
  rw [releaseLinkOn_eq_obj, releaseLinkOn_eq_obj]; exact h _ c

/-- Two stores agreeing up to a rewrite that keeps every object's release links
hold the same release links. -/
theorem ReleaseLinksAgree.of_map {st st' : SystemState} (g : KernelObject → KernelObject)
    (hg : ∀ o c, objReleaseLinkOn (some (g o)) c = objReleaseLinkOn (some o) c)
    (h : ∀ k : SeLe4n.ObjId, (st'.objects[k]?).map g = (st.objects[k]?).map g) :
    ReleaseLinksAgree st' st :=
  .of_objReleaseLinkOn fun k c => by
    have e := h k
    revert e
    cases st'.objects[k]? <;> cases st.objects[k]? <;> intro e
    · rfl
    · cases e
    · cases e
    · rename_i a b
      simp only [Option.map_some, Option.some.injEq] at e
      rw [← hg a c, e, hg b c]

/-- An insert whose object gives its slot's release links holds the release
links. -/
theorem ReleaseLinksAgree.insert {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hO : st'.objects = st.objects.insert k o)
    (h : ∀ c, objReleaseLinkOn (some o) c = objReleaseLinkOn st.objects[k]? c) :
    ReleaseLinksAgree st' st :=
  .of_objReleaseLinkOn fun x c => by
    rw [hO]
    by_cases hx : x = k
    · subst hx
      have e : (st.objects.insert x o)[x]? = some o :=
        RobinHood.RHTable.getElem?_insert_self st.objects x o hInv
      rw [e]; exact h c
    · have e : (st.objects.insert k o)[x]? = st.objects[x]? :=
        RobinHood.RHTable.getElem?_insert_ne st.objects k x o
          (by intro h'; exact hx (eq_of_beq h').symm) hInv
      rw [e]

/-! ## The agreement -/

/-- The contexts core `c`'s abstract release queue holds, in order. -/
noncomputable abbrev releaseIds (st : SystemState) (c : CoreId) : List SeLe4n.SchedContextId :=
  (st.scheduler.replenishQueueOnCore c).entries.map Prod.fst

/-- WS-ZA ZA6.3: core `c`'s release queue and the contexts agree — reading
from the core's head along the contexts' links gives the abstract queue's
contexts in order, each once; a context is on the queue exactly when its link
names core `c`; each link holds its entry's release time; and the core's count
is the queue's length. -/
-- A conjunction, not a structure, so a step that keeps the objects and the
-- scheduler (a record update of another field) keeps it definitionally, as the
-- run-queue agreement is kept; the five parts are read by name below.
def releaseQueueRefinedOnCore (st : SystemState) (c : CoreId) : Prop :=
  Chain (st.releaseNextOn c) (st.scheduler.releaseHeadOnCore c) (st.releaseIds c) ∧
  (st.releaseIds c).Nodup ∧
  (∀ s, st.releaseQueuedOn c s = true ↔ s ∈ st.releaseIds c) ∧
  (∀ e ∈ (st.scheduler.replenishQueueOnCore c).entries, st.releaseAtOn c e.1 = e.2) ∧
  st.scheduler.releaseCountOnCore c = (st.scheduler.replenishQueueOnCore c).entries.length

namespace releaseQueueRefinedOnCore

variable {st : SystemState} {c : CoreId}

/-- Reading from the head along the links meets the queue's contexts in order. -/
theorem chain (h : st.releaseQueueRefinedOnCore c) :
    Chain (st.releaseNextOn c) (st.scheduler.releaseHeadOnCore c) (st.releaseIds c) := h.1
/-- Each context is on the queue once. -/
theorem nodup (h : st.releaseQueueRefinedOnCore c) : (st.releaseIds c).Nodup := h.2.1
/-- A context is on the queue exactly when its link names the core. -/
theorem queued (h : st.releaseQueueRefinedOnCore c) :
    ∀ s, st.releaseQueuedOn c s = true ↔ s ∈ st.releaseIds c := h.2.2.1
/-- Each link holds its entry's release time. -/
theorem at_eq (h : st.releaseQueueRefinedOnCore c) :
    ∀ e ∈ (st.scheduler.replenishQueueOnCore c).entries, st.releaseAtOn c e.1 = e.2 := h.2.2.2.1
/-- The core's count is the queue's length. -/
theorem count (h : st.releaseQueueRefinedOnCore c) :
    st.scheduler.releaseCountOnCore c = (st.scheduler.replenishQueueOnCore c).entries.length :=
  h.2.2.2.2

end releaseQueueRefinedOnCore

/-- WS-ZA ZA6.3: every core's release queue agrees with the contexts. -/
def releaseQueueRefined (st : SystemState) : Prop := ∀ c, st.releaseQueueRefinedOnCore c

/-- A transition that leaves every release link, every queue, every head and
every count as they were keeps the agreement. -/
theorem releaseQueueRefined_of_frame {st st' : SystemState} (hL : ReleaseLinksAgree st' st)
    (hQ : st'.scheduler.replenishQueue = st.scheduler.replenishQueue)
    (hH : st'.scheduler.releaseHeadCode = st.scheduler.releaseHeadCode)
    (hC : st'.scheduler.releaseCount = st.scheduler.releaseCount)
    (h : st.releaseQueueRefined) : st'.releaseQueueRefined := by
  intro c
  have hc := h c
  have hRq : st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
    unfold SchedulerState.replenishQueueOnCore; rw [hQ]
  have hHd : st'.scheduler.releaseHeadOnCore c = st.scheduler.releaseHeadOnCore c := by
    unfold SchedulerState.releaseHeadOnCore; rw [hH]
  have hCt : st'.scheduler.releaseCountOnCore c = st.scheduler.releaseCountOnCore c := by
    unfold SchedulerState.releaseCountOnCore; rw [hC]
  have hIds : st'.releaseIds c = st.releaseIds c := by unfold releaseIds; rw [hRq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hL.nextOn c, hHd, hIds]; exact hc.chain
  · rw [hIds]; exact hc.nodup
  · intro s; rw [hL.queuedOn c, hIds]; exact hc.queued s
  · intro e he; rw [hL.atOn c]; rw [hRq] at he; exact hc.at_eq e he
  · rw [hCt, hRq]; exact hc.count

/-- **Empty release queues agree with contexts linked into none**: every core's
abstract queue empty, its head and count `0`, and no context linked on it. -/
theorem releaseQueueRefined_of_empty {st : SystemState}
    (hQ : ∀ c, (st.scheduler.replenishQueueOnCore c).entries = [])
    (hH : ∀ c, st.scheduler.releaseHeadOnCore c = 0)
    (hC : ∀ c, st.scheduler.releaseCountOnCore c = 0)
    (hL : ∀ c s, st.releaseQueuedOn c s = false) : st.releaseQueueRefined := by
  intro c
  have hIds : st.releaseIds c = [] := by unfold releaseIds; rw [hQ c]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hIds, hH c]; exact rfl
  · rw [hIds]; exact List.nodup_nil
  · intro s; rw [hIds, hL c s]; simp
  · intro e he; rw [hQ c] at he; cases he
  · rw [hC c, hQ c]; rfl

/-- The empty state's release queues agree with its (absent) contexts. -/
theorem default_releaseQueueRefined : (default : SystemState).releaseQueueRefined :=
  releaseQueueRefined_of_empty
    (fun c => by
      show ((default : SchedulerState).replenishQueueOnCore c).entries = []
      rw [(default_state_perCoreInitialized c).2.2.1]; rfl)
    (fun c => PerCoreVector.replicate_get _ _ c)
    (fun c => PerCoreVector.replicate_get _ _ c)
    (fun c s => by
      have h : (default : SystemState).objects[s.toObjId]? = none := by
        simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
      unfold releaseQueuedOn getSchedContext?; rw [h])

/-- ...in particular one that writes neither the objects nor the scheduler. -/
theorem releaseQueueRefined_of_objects_scheduler_eq {st st' : SystemState}
    (hO : st'.objects = st.objects) (hS : st'.scheduler = st.scheduler)
    (h : st.releaseQueueRefined) : st'.releaseQueueRefined :=
  releaseQueueRefined_of_frame (.of_objects_eq hO) (congrArg SchedulerState.replenishQueue hS)
    (congrArg SchedulerState.releaseHeadCode hS) (congrArg SchedulerState.releaseCount hS) h

/-- A context write that keeps the release fields keeps the agreement. -/
theorem releaseQueueRefined_mapSchedContextInPlace {st : SystemState} (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext)
    (hg : ∀ sc, (g sc).releaseCoreCode = sc.releaseCoreCode ∧
      (g sc).releaseNextCode = sc.releaseNextCode ∧ (g sc).releaseAt = sc.releaseAt)
    (h : st.releaseQueueRefined) : (st.mapSchedContextInPlace s g).releaseQueueRefined :=
  releaseQueueRefined_of_frame (.mapSchedContextInPlace st s g hg) rfl rfl rfl h

/-! ## Walks along a core's links

Each walk reads the contexts directly, with no link function built, and is
the corresponding `ReleaseChain` walk over `releaseNextOn` / `releaseAtOn`. -/

/-- The contexts read from code `h` along core `c`'s links, at most `f` of them. -/
def releaseWalk (st : SystemState) (c : CoreId) : Nat → Nat → List SeLe4n.SchedContextId
  | 0, _ => []
  | f + 1, h => if h = 0 then [] else decode h :: releaseWalk st c f (st.releaseNextOn c (decode h))

theorem releaseWalk_eq (st : SystemState) (c : CoreId) :
    ∀ f h, st.releaseWalk c f h = walk (st.releaseNextOn c) f h
  | 0, _ => rfl
  | f + 1, h => by
    simp only [releaseWalk, walk, releaseWalk_eq st c f]

/-- The code of the member of core `c`'s queue after which a context released
at `t` goes (`p` for the head). -/
def releasePredBefore (st : SystemState) (c : CoreId) (t : Nat) : Nat → Nat → Nat → Nat
  | 0, p, _ => p
  | f + 1, p, h =>
    if h = 0 then p
    else if t < st.releaseAtOn c (decode h) then p
    else releasePredBefore st c t f h (st.releaseNextOn c (decode h))

theorem releasePredBefore_eq (st : SystemState) (c : CoreId) (t : Nat) :
    ∀ f p h, st.releasePredBefore c t f p h =
      predBefore (st.releaseNextOn c) (st.releaseAtOn c) t f p h
  | 0, _, _ => rfl
  | f + 1, p, h => by
    simp only [releasePredBefore, predBefore, releasePredBefore_eq st c t f]

/-- The code of `s`'s predecessor on core `c`'s queue (`p` for the head). -/
def releasePredOf (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    Nat → Nat → Nat → Nat
  | 0, p, _ => p
  | f + 1, p, h =>
    if h = 0 then p else if decode h = s then p
    else releasePredOf st c s f h (st.releaseNextOn c (decode h))

theorem releasePredOf_eq (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    ∀ f p h, st.releasePredOf c s f p h = predOf (st.releaseNextOn c) s f p h
  | 0, _, _ => rfl
  | f + 1, p, h => by
    simp only [releasePredOf, predOf, releasePredOf_eq st c s f]

/-! ## The edits -/

/-- WS-ZA ZA6.3: unlink `s` from core `c`'s release queue through the links:
its predecessor (or the head) takes over its successor, it is marked on no
core, and the count drops.  A context not on `c`'s queue is left as it is. -/
def releaseUnlinkOn (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) : SystemState :=
  if st.releaseQueuedOn c s then
    let count := st.scheduler.releaseCountOnCore c
    let p := st.releasePredOf c s count 0 (st.scheduler.releaseHeadOnCore c)
    let n := st.releaseNextOn c s
    let st1 := st.mapSchedContextInPlace s SchedContext.leaveRelease
    let st2 := if p = 0 then { st1 with scheduler := st1.scheduler.setReleaseHeadOnCore c n }
      else st1.mapSchedContextInPlace (decode p) (SchedContext.withReleaseNext n)
    { st2 with scheduler := st2.scheduler.setReleaseCountOnCore c (count - 1) }
  else st

/-- WS-ZA ZA6.3: `releaseUnlinkOn`'s object writes, handed the predecessor `p`
and the successor `n`: `s` marked on no queue, and its predecessor (when it has
one) linked to `n`, each context in its slot. -/
@[noinline] def releaseUnlinkObjects (objs : RHTable SeLe4n.ObjId KernelObject)
    (s : SeLe4n.SchedContextId) (p n : Nat) : RHTable SeLe4n.ObjId KernelObject :=
  let o := objs.mapValueAt s.toObjId (mapSchedContextObject SchedContext.leaveRelease)
  if p = 0 then o
  else o.mapValueAt (decode p).toObjId (mapSchedContextObject (SchedContext.withReleaseNext n))

/-- WS-ZA ZA6.3: `releaseUnlinkOn`'s scheduler writes: the head takes over `n`
when `s` was the head (`p = 0`), and the count drops. -/
@[noinline] def releaseUnlinkScheduler (sch : SchedulerState) (c : CoreId) (count p n : Nat) :
    SchedulerState :=
  (if p = 0 then sch.setReleaseHeadOnCore c n else sch).setReleaseCountOnCore c (count - 1)

/-- WS-ZA ZA6.3: `releaseUnlinkOn`'s writes, handed the count, the predecessor
`p` and the successor `n` it read: one record update whose fields are calls
(`releaseUnlinkObjects`, `releaseUnlinkScheduler`), so every read is taken
before the state is written and the update reuses the state's cell. -/
@[noinline] def releaseUnlinkWrite (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (count p n : Nat) : SystemState :=
  { st with objects := releaseUnlinkObjects st.objects s p n
            scheduler := releaseUnlinkScheduler st.scheduler c count p n }

/-- WS-ZA ZA6.3: the compiled `releaseUnlinkOn`: the links read, then written by
one call (`releaseUnlinkWrite`).  Compiled as written, the specification took
the state's fields apart before its last read of the state, so its write built
a new state.  Proven equal (`releaseUnlinkOn_eq_impl`). -/
def releaseUnlinkOnImpl (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    SystemState :=
  if st.releaseQueuedOn c s then
    let count := st.scheduler.releaseCountOnCore c
    st.releaseUnlinkWrite c s count
      (st.releasePredOf c s count 0 (st.scheduler.releaseHeadOnCore c)) (st.releaseNextOn c s)
  else st

@[csimp] theorem releaseUnlinkOn_eq_impl : @releaseUnlinkOn = @releaseUnlinkOnImpl := by
  funext st c s
  unfold releaseUnlinkOn releaseUnlinkOnImpl releaseUnlinkWrite releaseUnlinkObjects
    releaseUnlinkScheduler mapSchedContextInPlace
  split
  · dsimp only
    split <;> rfl
  · rfl

/-- WS-ZA ZA6.3: drop `s` from core `c`'s release queue — the links unlinked
(`releaseUnlinkOn`) and the abstract queue's removal written. -/
def releaseRemoveOn (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) : SystemState :=
  let st' := st.releaseUnlinkOn c s
  let q := (st.scheduler.replenishQueueOnCore c).remove s
  { st' with scheduler := st'.scheduler.setReplenishQueueOnCore c q }

/-- WS-ZA ZA6.3: link `s`, released at `t`, into core `c`'s release queue at
its sorted place — after every member released no later than `t`, as
`ReplenishQueue.insertSorted` places the entry — and count it. -/
def releaseLinkIn (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) (t : Nat) :
    SystemState :=
  let head := st.scheduler.releaseHeadOnCore c
  let count := st.scheduler.releaseCountOnCore c
  let p := st.releasePredBefore c t count 0 head
  let n := if p = 0 then head else st.releaseNextOn c (decode p)
  let st1 := st.mapSchedContextInPlace s (SchedContext.joinRelease c n t)
  let st2 := if p = 0 then { st1 with scheduler := st1.scheduler.setReleaseHeadOnCore c (code s) }
    else st1.mapSchedContextInPlace (decode p) (SchedContext.withReleaseNext (code s))
  { st2 with scheduler := st2.scheduler.setReleaseCountOnCore c (count + 1) }

/-- WS-ZA ZA6.3: `releaseLinkIn`'s object writes, handed the predecessor `p` and
the successor `n`: `s` linked to `n` at `t` on core `c`, and its predecessor
(when it has one) linked to `s`, each context in its slot. -/
@[noinline] def releaseLinkObjects (objs : RHTable SeLe4n.ObjId KernelObject) (c : CoreId)
    (s : SeLe4n.SchedContextId) (t p n : Nat) : RHTable SeLe4n.ObjId KernelObject :=
  let o := objs.mapValueAt s.toObjId (mapSchedContextObject (SchedContext.joinRelease c n t))
  if p = 0 then o
  else o.mapValueAt (decode p).toObjId (mapSchedContextObject (SchedContext.withReleaseNext (code s)))

/-- WS-ZA ZA6.3: `releaseLinkIn`'s scheduler writes: `s` is the head when it has
no predecessor (`p = 0`), and the count rises. -/
@[noinline] def releaseLinkScheduler (sch : SchedulerState) (c : CoreId)
    (s : SeLe4n.SchedContextId) (count p : Nat) : SchedulerState :=
  (if p = 0 then sch.setReleaseHeadOnCore c (code s) else sch).setReleaseCountOnCore c (count + 1)

/-- WS-ZA ZA6.3: `releaseLinkIn`'s writes, handed the count, the predecessor `p`
and the successor `n` it read: one record update whose fields are calls, as
`releaseUnlinkWrite` is. -/
@[noinline] def releaseLinkWrite (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (t count p n : Nat) : SystemState :=
  { st with objects := releaseLinkObjects st.objects c s t p n
            scheduler := releaseLinkScheduler st.scheduler c s count p }

/-- WS-ZA ZA6.3: the compiled `releaseLinkIn`: the place read, then written by one
call (`releaseLinkWrite`).  Proven equal (`releaseLinkIn_eq_impl`). -/
def releaseLinkInImpl (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) (t : Nat) :
    SystemState :=
  let head := st.scheduler.releaseHeadOnCore c
  let count := st.scheduler.releaseCountOnCore c
  let p := st.releasePredBefore c t count 0 head
  st.releaseLinkWrite c s t count p (if p = 0 then head else st.releaseNextOn c (decode p))

@[csimp] theorem releaseLinkIn_eq_impl : @releaseLinkIn = @releaseLinkInImpl := by
  funext st c s t
  unfold releaseLinkIn releaseLinkInImpl releaseLinkWrite releaseLinkObjects releaseLinkScheduler
    mapSchedContextInPlace
  dsimp only
  split <;> rfl

/-- Does context `s`'s link name a core?  Read from the context alone. -/
@[inline] def releaseQueuedAnywhere (st : SystemState) (s : SeLe4n.SchedContextId) : Bool :=
  match st.getSchedContext? s with
  | some sc => sc.releaseCoreCode != 0 && decide (sc.releaseCoreCode ≤ Concurrency.numCores)
  | none => false

/-- The insert of a context on no queue: linked in and the abstract queue's
insert written. -/
def releaseInsertFresh (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) (t : Nat) :
    SystemState :=
  let st' := st.releaseLinkIn c s t
  let q := (st.scheduler.replenishQueueOnCore c).insert s t
  { st' with scheduler := st'.scheduler.setReplenishQueueOnCore c q }

/-- WS-ZA ZA6.3: queue context `s`'s release at `t` on core `c` — linked in at
its sorted place and the abstract queue's insert written.  A context already
on a release queue, or no context, is left as it is: every caller queues a
context that is on none (seL4's `tcbReleaseEnqueue` asserts the same). -/
def releaseInsertOn (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) (t : Nat) :
    SystemState :=
  if st.releaseQueuedAnywhere s || (st.getSchedContext? s).isNone then st
  else st.releaseInsertFresh c s t

/-! ## What the edits write -/

@[simp] theorem _root_.SeLe4n.Kernel.SchedContext.releaseLinkOn_leaveRelease (sc : SchedContext)
    (c : CoreId) : sc.leaveRelease.releaseLinkOn c = none := by
  simp [SchedContext.leaveRelease, SchedContext.releaseLinkOn]

theorem _root_.SeLe4n.Kernel.SchedContext.releaseLinkOn_withReleaseNext (sc : SchedContext)
    (n : Nat) (c : CoreId) :
    (sc.withReleaseNext n).releaseLinkOn c = (sc.releaseLinkOn c).map fun l => (n, l.2) := by
  unfold SchedContext.withReleaseNext SchedContext.releaseLinkOn
  by_cases h : sc.releaseCoreCode = c.val + 1 <;> simp [h]

theorem _root_.SeLe4n.Kernel.SchedContext.releaseLinkOn_joinRelease (sc : SchedContext)
    (c c' : CoreId) (n t : Nat) :
    (sc.joinRelease c n t).releaseLinkOn c' = if c' = c then some (n, t) else none := by
  unfold SchedContext.joinRelease SchedContext.releaseLinkOn
  by_cases h : c' = c
  · subst h; simp
  · have : ¬ (c.val = c'.val) := fun e => h (Fin.ext e.symm)
    simp [h, this]

theorem releaseLinkOn_mapSchedContextInPlace_self (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) (c : CoreId) :
    (st.mapSchedContextInPlace s g).releaseLinkOn c s =
      (st.getSchedContext? s).bind fun sc => (g sc).releaseLinkOn c := by
  unfold releaseLinkOn
  rw [mapSchedContextInPlace_getSchedContext?_self]
  cases st.getSchedContext? s <;> rfl

theorem releaseLinkOn_mapSchedContextInPlace_ne (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) (c : CoreId) {y : SeLe4n.SchedContextId} (hy : y ≠ s) :
    (st.mapSchedContextInPlace s g).releaseLinkOn c y = st.releaseLinkOn c y :=
  releaseLinkOn_of_getSchedContext? (mapSchedContextInPlace_getSchedContext?_ne _ _ _ hy) c

@[simp] theorem releaseLinkOn_withScheduler (st : SystemState) (sch : SchedulerState) (c : CoreId)
    (s : SeLe4n.SchedContextId) :
    ({ st with scheduler := sch } : SystemState).releaseLinkOn c s = st.releaseLinkOn c s := rfl

@[simp] theorem releaseNextOn_withScheduler (st : SystemState) (sch : SchedulerState) (c : CoreId)
    (s : SeLe4n.SchedContextId) :
    ({ st with scheduler := sch } : SystemState).releaseNextOn c s = st.releaseNextOn c s := rfl

@[simp] theorem releaseAtOn_withScheduler (st : SystemState) (sch : SchedulerState) (c : CoreId)
    (s : SeLe4n.SchedContextId) :
    ({ st with scheduler := sch } : SystemState).releaseAtOn c s = st.releaseAtOn c s := rfl

@[simp] theorem releaseQueuedOn_withScheduler (st : SystemState) (sch : SchedulerState) (c : CoreId)
    (s : SeLe4n.SchedContextId) :
    ({ st with scheduler := sch } : SystemState).releaseQueuedOn c s = st.releaseQueuedOn c s := rfl

/-- The link function a core's links read as. -/
def nextOfLinks (L : SeLe4n.SchedContextId → Option (Nat × Nat)) (x : SeLe4n.SchedContextId) : Nat :=
  match L x with | some (n, _) => n | none => 0

theorem releaseNextOn_eq_nextOfLinks (st : SystemState) (c : CoreId) :
    st.releaseNextOn c = nextOfLinks (st.releaseLinkOn c) :=
  funext fun s => releaseNextOn_eq st c s

/-- A per-core frame: core `c`'s links, queue, head and count as they were keep
core `c`'s agreement. -/
theorem releaseQueueRefinedOnCore_of_frame {st st' : SystemState} {c : CoreId}
    (hL : ∀ s, st'.releaseLinkOn c s = st.releaseLinkOn c s)
    (hQ : (st'.scheduler.replenishQueueOnCore c).entries = (st.scheduler.replenishQueueOnCore c).entries)
    (hH : st'.scheduler.releaseHeadOnCore c = st.scheduler.releaseHeadOnCore c)
    (hC : st'.scheduler.releaseCountOnCore c = st.scheduler.releaseCountOnCore c)
    (h : st.releaseQueueRefinedOnCore c) : st'.releaseQueueRefinedOnCore c := by
  have hN : st'.releaseNextOn c = st.releaseNextOn c := funext fun s => by
    rw [releaseNextOn_eq, releaseNextOn_eq, hL s]
  have hA : st'.releaseAtOn c = st.releaseAtOn c := funext fun s => by
    rw [releaseAtOn_eq, releaseAtOn_eq, hL s]
  have hQd : st'.releaseQueuedOn c = st.releaseQueuedOn c := funext fun s => by
    rw [releaseQueuedOn_eq, releaseQueuedOn_eq, hL s]
  have hIds : st'.releaseIds c = st.releaseIds c := by unfold releaseIds; rw [hQ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hN, hH, hIds]; exact h.chain
  · rw [hIds]; exact h.nodup
  · intro s; rw [hQd, hIds]; exact h.queued s
  · intro e he; rw [hA]; rw [hQ] at he; exact h.at_eq e he
  · rw [hC, hQ]; exact h.count

theorem releaseLinkOn_ne_core {st : SystemState} {c c' : CoreId} (hne : c' ≠ c)
    {x : SeLe4n.SchedContextId} (hq : (st.releaseLinkOn c x).isSome) : st.releaseLinkOn c' x = none := by
  unfold releaseLinkOn at hq ⊢
  cases h : st.getSchedContext? x with
  | none => rfl
  | some sc =>
    rw [h] at hq
    unfold SchedContext.releaseLinkOn at hq ⊢
    by_cases hc : sc.releaseCoreCode = c.val + 1
    · have : ¬ sc.releaseCoreCode = c'.val + 1 := fun e => hne (Fin.ext (by omega))
      simp [this]
    · simp [hc] at hq

/-- Unlinking writes `s`'s link away and its predecessor's successor; every
other context's link on every core is as it was. -/
theorem releaseLinkOn_releaseUnlinkOn (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (hq : st.releaseQueuedOn c s = true) (c' : CoreId) (y : SeLe4n.SchedContextId) :
    (st.releaseUnlinkOn c s).releaseLinkOn c' y =
      let p := st.releasePredOf c s (st.scheduler.releaseCountOnCore c) 0
        (st.scheduler.releaseHeadOnCore c)
      if y = s then none
      else if p ≠ 0 ∧ y = decode p then
        (st.releaseLinkOn c' y).map fun l => (st.releaseNextOn c s, l.2)
      else st.releaseLinkOn c' y := by
  unfold releaseUnlinkOn
  rw [if_pos hq]
  dsimp only
  rw [releaseLinkOn_withScheduler]
  generalize st.releasePredOf c s (st.scheduler.releaseCountOnCore c) 0
    (st.scheduler.releaseHeadOnCore c) = p
  have hS : ∀ c'', (st.mapSchedContextInPlace s SchedContext.leaveRelease).releaseLinkOn c'' s = none := by
    intro c''
    rw [releaseLinkOn_mapSchedContextInPlace_self]
    cases st.getSchedContext? s <;> simp
  by_cases hp : p = 0
  · simp only [hp, if_true, releaseLinkOn_withScheduler, ne_eq, not_true_eq_false, false_and,
      if_false]
    by_cases hy : y = s
    · subst hy; simp [hS]
    · simp [hy, releaseLinkOn_mapSchedContextInPlace_ne _ _ _ _ hy]
  · simp only [hp, if_false, ne_eq, not_false_eq_true, true_and]
    by_cases hy : y = s
    · subst hy
      by_cases hd : y = decode p
      · rw [← hd, releaseLinkOn_mapSchedContextInPlace_self, mapSchedContextInPlace_getSchedContext?_self]
        cases st.getSchedContext? y <;> simp [SchedContext.releaseLinkOn_withReleaseNext]
      · rw [releaseLinkOn_mapSchedContextInPlace_ne _ _ _ _ hd, hS]; simp
    · by_cases hd : y = decode p
      · subst hd
        rw [releaseLinkOn_mapSchedContextInPlace_self]
        rw [mapSchedContextInPlace_getSchedContext?_ne _ _ _ hy]
        simp only [hy, if_false, if_true]
        unfold releaseLinkOn
        cases st.getSchedContext? (decode p) with
        | none => rfl
        | some sc => simp [SchedContext.releaseLinkOn_withReleaseNext]
      · rw [releaseLinkOn_mapSchedContextInPlace_ne _ _ _ _ hd,
          releaseLinkOn_mapSchedContextInPlace_ne _ _ _ _ hy]
        simp [hy, hd]

theorem releaseUnlinkOn_scheduler (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    (st.releaseUnlinkOn c s).scheduler =
      if st.releaseQueuedOn c s then
        (if st.releasePredOf c s (st.scheduler.releaseCountOnCore c) 0
            (st.scheduler.releaseHeadOnCore c) = 0 then
          st.scheduler.setReleaseHeadOnCore c (st.releaseNextOn c s)
        else st.scheduler).setReleaseCountOnCore c (st.scheduler.releaseCountOnCore c - 1)
      else st.scheduler := by
  unfold releaseUnlinkOn
  split
  · dsimp only; split <;> rfl
  · rfl

/-- Unlinking writes only the objects and the scheduler. -/
theorem releaseUnlinkOn_eta (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    st.releaseUnlinkOn c s = { st with
      objects := (st.releaseUnlinkOn c s).objects
      scheduler := (st.releaseUnlinkOn c s).scheduler } := by
  unfold releaseUnlinkOn
  split
  · dsimp only; split <;> rfl
  · rfl

theorem releaseUnlinkOn_replenishQueue (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    (st.releaseUnlinkOn c s).scheduler.replenishQueue = st.scheduler.replenishQueue := by
  rw [releaseUnlinkOn_scheduler]; split
  · split <;> rfl
  · rfl

/-! ### List facts the edits rest on -/

/-- A context named in an entry list splits it at that entry. -/
theorem entries_split_of_mem {es : List (SeLe4n.SchedContextId × Nat)} {s : SeLe4n.SchedContextId}
    (h : s ∈ es.map Prod.fst) :
    ∃ Ae t Be, es = Ae ++ (s, t) :: Be := by
  obtain ⟨⟨s', t⟩, he, rfl⟩ := List.mem_map.mp h
  obtain ⟨Ae, Be, rfl⟩ := List.append_of_mem he
  exact ⟨Ae, t, Be, rfl⟩

/-- Removing a context from a duplicate-free entry list drops its one entry. -/
theorem filter_ne_of_split {Ae Be : List (SeLe4n.SchedContextId × Nat)} {s : SeLe4n.SchedContextId}
    {t : Nat} (hnd : ((Ae ++ (s, t) :: Be).map Prod.fst).Nodup) :
    (Ae ++ (s, t) :: Be).filter (fun (id, _) => !(id == s)) = Ae ++ Be := by
  rw [List.map_append, List.map_cons, List.nodup_append] at hnd
  obtain ⟨_, hndB, hdis⟩ := hnd
  have hA : ∀ e ∈ Ae, e.1 ≠ s := fun e he h =>
    hdis e.1 (List.mem_map.mpr ⟨e, he, rfl⟩) s (List.mem_cons_self ..) h
  have hB : ∀ e ∈ Be, e.1 ≠ s := fun e he h =>
    (List.nodup_cons.mp hndB).1 (List.mem_map.mpr ⟨e, he, h⟩)
  rw [List.filter_append, List.filter_cons]
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, if_false]
  rw [List.filter_eq_self.mpr (fun e he => by simpa using hA e he),
    List.filter_eq_self.mpr (fun e he => by simpa using hB e he)]

/-- Removing a context a list does not name leaves its entries as they are. -/
theorem filter_ne_of_not_mem {es : List (SeLe4n.SchedContextId × Nat)} {s : SeLe4n.SchedContextId}
    (h : s ∉ es.map Prod.fst) : es.filter (fun (id, _) => !(id == s)) = es :=
  List.filter_eq_self.mpr fun e he => by
    have : e.1 ≠ s := fun h' => h (List.mem_map.mpr ⟨e, he, h'⟩)
    simpa using this

/-! ### Removal keeps the agreement -/

theorem releaseLinkOn_isSome_iff_queued (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    (st.releaseLinkOn c s).isSome = true ↔ st.releaseQueuedOn c s = true := by
  rw [releaseQueuedOn_eq]

theorem nextOfLinks_map_some {L : SeLe4n.SchedContextId → Option (Nat × Nat)} {z : SeLe4n.SchedContextId}
    {n : Nat} (h : (L z).isSome) :
    (match (L z).map (fun l => (n, l.2)) with | some (m, _) => m | none => 0) = n := by
  cases e : L z with
  | none => rw [e] at h; cases h
  | some l => rfl

/-- `lastCode 0 A` names `A`'s last member, when there is one. -/
theorem lastCode_ne_zero_and_iff (A : List SeLe4n.SchedContextId) (y : SeLe4n.SchedContextId) :
    (lastCode 0 A ≠ 0 ∧ y = decode (lastCode 0 A)) ↔ A.getLast? = some y := by
  rw [lastCode_eq_getLast?]
  cases A.getLast? with
  | none => simp
  | some z => simp [eq_comm, Ne.symm (code_ne_zero z)]

/-- The queued case of removal: the unlink is `chain_unlink` at `s`'s place. -/
theorem releaseRemoveOn_refined_of_queued {st : SystemState} (h : st.releaseQueueRefined)
    (c : CoreId) (s : SeLe4n.SchedContextId) (hq : st.releaseQueuedOn c s = true) (c' : CoreId) :
    (st.releaseRemoveOn c s).releaseQueueRefinedOnCore c' := by
  have hc := h c
  obtain ⟨Ae, t, Be, hes⟩ := entries_split_of_mem ((hc.queued s).mp hq)
  have hIds : st.releaseIds c = Ae.map Prod.fst ++ s :: Be.map Prod.fst := by
    simp only [releaseIds, hes, List.map_append, List.map_cons]
  generalize hA : Ae.map Prod.fst = A at hIds
  generalize hB : Be.map Prod.fst = B at hIds
  have hnd : (A ++ s :: B).Nodup := hIds ▸ hc.nodup
  have hsA : s ∉ A := fun m => (List.nodup_append.mp hnd).2.2 s m s (List.mem_cons_self ..) rfl
  have hsB : s ∉ B := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
  have hchain : Chain (st.releaseNextOn c) (st.scheduler.releaseHeadOnCore c) (A ++ s :: B) :=
    hIds ▸ hc.chain
  have hlen : (A ++ s :: B).length ≤ st.scheduler.releaseCountOnCore c := by
    rw [hc.count, ← hIds]; simp [releaseIds]
  have hp : st.releasePredOf c s (st.scheduler.releaseCountOnCore c) 0
      (st.scheduler.releaseHeadOnCore c) = lastCode 0 A := by
    rw [releasePredOf_eq]; exact hchain.predOf_eq hsA hlen 0
  -- what the unlink wrote, link by link
  have hLk : ∀ c'' y, (st.releaseRemoveOn c s).releaseLinkOn c'' y =
      if y = s then none
      else if A.getLast? = some y then
        (st.releaseLinkOn c'' y).map fun l => (st.releaseNextOn c s, l.2)
      else st.releaseLinkOn c'' y := fun c'' y => by
    have e := releaseLinkOn_releaseUnlinkOn st c s hq c'' y
    rw [hp] at e
    show (st.releaseUnlinkOn c s).releaseLinkOn c'' y = _
    rw [e]; dsimp only
    by_cases hy : y = s
    · simp [hy]
    · rw [if_neg hy, if_neg hy]
      by_cases hl : A.getLast? = some y
      · rw [if_pos ((lastCode_ne_zero_and_iff A y).mpr hl), if_pos hl]
      · rw [if_neg (fun e => hl ((lastCode_ne_zero_and_iff A y).mp e)), if_neg hl]
  have hMemQ : ∀ y ∈ A ++ s :: B, (st.releaseLinkOn c y).isSome = true := fun y hy => by
    rw [releaseLinkOn_isSome_iff_queued, hc.queued, hIds]; exact hy
  have hLastMem : ∀ z, A.getLast? = some z → z ∈ A := fun z hz => List.mem_of_getLast? hz
  -- the scheduler the removal leaves
  have hSch : (st.releaseRemoveOn c s).scheduler = (st.releaseUnlinkOn c s).scheduler.setReplenishQueueOnCore c
      ((st.scheduler.replenishQueueOnCore c).remove s) := rfl
  have hUs := releaseUnlinkOn_scheduler st c s
  rw [if_pos hq, hp] at hUs
  have hHd : ∀ d, (st.releaseRemoveOn c s).scheduler.releaseHeadOnCore d =
      if d = c ∧ lastCode 0 A = 0 then st.releaseNextOn c s else st.scheduler.releaseHeadOnCore d := by
    intro d
    rw [hSch, SchedulerState.setReplenishQueueOnCore_releaseHeadOnCore, hUs,
      SchedulerState.setReleaseCountOnCore_releaseHeadOnCore']
    by_cases h0 : lastCode 0 A = 0
    · rw [if_pos h0]
      by_cases hd : d = c
      · subst hd; simp [h0]
      · rw [SchedulerState.setReleaseHeadOnCore_releaseHeadOnCore_ne _ _ _ _ (Ne.symm hd)]; simp [hd]
    · rw [if_neg h0]; simp [h0]
  have hCt : ∀ d, (st.releaseRemoveOn c s).scheduler.releaseCountOnCore d =
      if d = c then st.scheduler.releaseCountOnCore c - 1 else st.scheduler.releaseCountOnCore d := by
    intro d
    rw [hSch, SchedulerState.setReplenishQueueOnCore_releaseCountOnCore, hUs]
    by_cases hd : d = c
    · subst hd; simp
    · rw [if_neg hd, SchedulerState.setReleaseCountOnCore_releaseCountOnCore_ne _ _ _ _ (Ne.symm hd)]
      split <;> simp
  rcases Decidable.em (c' = c) with rfl | hne
  · have hndE : ((Ae ++ (s, t) :: Be).map Prod.fst).Nodup := by
      have := hc.nodup; simp only [releaseIds, hes] at this; exact this
    have hQ' : ((st.releaseRemoveOn c' s).scheduler.replenishQueueOnCore c').entries = Ae ++ Be := by
      rw [hSch, SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self]
      show List.filter _ _ = _
      rw [hes]; exact filter_ne_of_split hndE
    have hIds' : (st.releaseRemoveOn c' s).releaseIds c' = A ++ B := by
      unfold releaseIds; rw [hQ', List.map_append, hA, hB]
    have hne_s : ∀ z ∈ A ++ B, z ≠ s := fun z hz e => by
      subst e; simp only [List.mem_append] at hz
      exact hz.elim hsA hsB
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hIds']
      have hU := chain_unlink (nx' := (st.releaseRemoveOn c' s).releaseNextOn c') hchain hnd
        (fun z hz hzl => by
          rw [releaseNextOn_eq, releaseNextOn_eq, hLk, if_neg (hne_s z hz), if_neg hzl])
        (fun z hz => by
          have hzs : z ≠ s := fun e => hsA (e ▸ hLastMem z hz)
          rw [releaseNextOn_eq, hLk, if_neg hzs, if_pos hz,
            nextOfLinks_map_some (hMemQ z (List.mem_append_left _ (hLastMem z hz)))]
          exact hchain.next_eq)
      have hH : (st.releaseRemoveOn c' s).scheduler.releaseHeadOnCore c' =
          firstCode (firstCode 0 B) A := by
        rw [hHd]
        by_cases h0 : lastCode 0 A = 0
        · rw [if_pos ⟨rfl, h0⟩]
          obtain rfl := (lastCode_zero_eq_zero_iff A).mp h0
          exact hchain.next_eq
        · rw [if_neg (fun e => h0 e.2), hchain.head_eq]
          have hAne : A ≠ [] := fun e => h0 ((lastCode_zero_eq_zero_iff A).mpr e)
          cases A with
          | nil => exact absurd rfl hAne
          | cons x r => rfl
      rw [hH]; exact hU
    · rw [hIds']
      exact hnd.sublist (List.Sublist.append_left (List.sublist_cons_self s B) A)
    · intro y
      rw [releaseQueuedOn_eq, hLk, hIds']
      by_cases hy : y = s
      · subst hy; simp only [if_true, Option.isSome_none, Bool.false_eq_true, false_iff]
        intro m; exact hne_s _ m rfl
      · rw [if_neg hy]
        have hiff : (st.releaseLinkOn c' y).isSome = true ↔ y ∈ A ++ B := by
          rw [releaseLinkOn_isSome_iff_queued, hc.queued, hIds]; simp [hy]
        split
        · rw [Option.isSome_map]; exact hiff
        · exact hiff
    · intro e he
      rw [hQ'] at he
      have he1 : e.1 ∈ A ++ B := by
        rw [← hA, ← hB, ← List.map_append]; exact List.mem_map_of_mem he
      have heo : e ∈ (st.scheduler.replenishQueueOnCore c').entries := by
        rw [hes]; simp only [List.mem_append, List.mem_cons] at he ⊢
        exact he.elim Or.inl (fun h => Or.inr (Or.inr h))
      have hold := hc.at_eq e heo
      rw [releaseAtOn_eq] at hold ⊢
      rw [hLk, if_neg (hne_s _ he1)]
      by_cases hl : A.getLast? = some e.1
      · rw [if_pos hl]
        rcases hL : st.releaseLinkOn c' e.1 with _ | ⟨n, a⟩ <;> rw [hL] at hold <;> simpa using hold
      · rw [if_neg hl]; exact hold
    · rw [hCt, if_pos rfl, hQ', hc.count, hes]; simp
  · have hLc : ∀ y, (st.releaseRemoveOn c s).releaseLinkOn c' y = st.releaseLinkOn c' y := by
      intro y
      rw [hLk]
      by_cases hy : y = s
      · subst hy; rw [if_pos rfl]
        exact (releaseLinkOn_ne_core hne (hMemQ y (by simp))).symm
      · rw [if_neg hy]
        split
        · rename_i hl
          rw [releaseLinkOn_ne_core hne (hMemQ y (List.mem_append_left _ (hLastMem y hl)))]; rfl
        · rfl
    refine releaseQueueRefinedOnCore_of_frame hLc ?_ ?_ ?_ (h c')
    · rw [hSch, SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ (Ne.symm hne)]
      unfold SchedulerState.replenishQueueOnCore; rw [releaseUnlinkOn_replenishQueue]
    · rw [hHd]; simp [hne]
    · rw [hCt]; simp [hne]

/-- **Removing a context keeps every core's agreement.** -/
theorem releaseRemoveOn_refined {st : SystemState} (h : st.releaseQueueRefined) (c : CoreId)
    (s : SeLe4n.SchedContextId) : (st.releaseRemoveOn c s).releaseQueueRefined := by
  intro c'
  have hL : ∀ c'' y, (st.releaseRemoveOn c s).releaseLinkOn c'' y =
      (st.releaseUnlinkOn c s).releaseLinkOn c'' y := fun _ _ => rfl
  have hSch : (st.releaseRemoveOn c s).scheduler = (st.releaseUnlinkOn c s).scheduler.setReplenishQueueOnCore c
      ((st.scheduler.replenishQueueOnCore c).remove s) := rfl
  have hQne : c' ≠ c → (st.releaseRemoveOn c s).scheduler.replenishQueueOnCore c' =
      st.scheduler.replenishQueueOnCore c' := fun hne => by
    rw [hSch, SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ (Ne.symm hne)]
    unfold SchedulerState.replenishQueueOnCore; rw [releaseUnlinkOn_replenishQueue]
  have hQc : (st.releaseRemoveOn c s).scheduler.replenishQueueOnCore c =
      (st.scheduler.replenishQueueOnCore c).remove s := by
    rw [hSch, SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self]
  by_cases hq : st.releaseQueuedOn c s = true
  · exact releaseRemoveOn_refined_of_queued h c s hq c'
  · have hU : st.releaseUnlinkOn c s = st := by unfold releaseUnlinkOn; rw [if_neg hq]
    have hL' : ∀ c'' y, (st.releaseRemoveOn c s).releaseLinkOn c'' y = st.releaseLinkOn c'' y :=
      fun c'' y => by rw [hL, hU]
    have hHd : ∀ d, (st.releaseRemoveOn c s).scheduler.releaseHeadOnCore d =
        st.scheduler.releaseHeadOnCore d := fun d => by
      rw [hSch, SchedulerState.setReplenishQueueOnCore_releaseHeadOnCore, hU]
    have hCt : ∀ d, (st.releaseRemoveOn c s).scheduler.releaseCountOnCore d =
        st.scheduler.releaseCountOnCore d := fun d => by
      rw [hSch, SchedulerState.setReplenishQueueOnCore_releaseCountOnCore, hU]
    by_cases hc : c' = c
    · subst hc
      refine releaseQueueRefinedOnCore_of_frame (hL' c') ?_ (hHd c') (hCt c') (h c')
      rw [hQc]
      exact filter_ne_of_not_mem (fun hm => hq ((h c').queued s |>.mpr hm))
    · exact releaseQueueRefinedOnCore_of_frame (hL' c') (by rw [hQne hc]) (hHd c') (hCt c') (h c')

/-! ### Insertion keeps the agreement -/

/-- An entry list whose members' release times the links hold reads the same
prefix through the links as through the entries. -/
theorem map_fst_takeWhile {es : List (SeLe4n.SchedContextId × Nat)} {tm : SeLe4n.SchedContextId → Nat}
    (h : ∀ e ∈ es, tm e.1 = e.2) (q : Nat → Bool) :
    (es.map Prod.fst).takeWhile (fun x => q (tm x)) = (es.takeWhile fun e => q e.2).map Prod.fst := by
  induction es with
  | nil => rfl
  | cons e r ih =>
    have he := h e (List.mem_cons_self ..)
    simp only [List.map_cons, List.takeWhile_cons, he]
    split
    · rw [List.map_cons, ih fun e' m => h e' (List.mem_cons_of_mem _ m)]
    · rfl

theorem map_fst_dropWhile {es : List (SeLe4n.SchedContextId × Nat)} {tm : SeLe4n.SchedContextId → Nat}
    (h : ∀ e ∈ es, tm e.1 = e.2) (q : Nat → Bool) :
    (es.map Prod.fst).dropWhile (fun x => q (tm x)) = (es.dropWhile fun e => q e.2).map Prod.fst := by
  induction es with
  | nil => rfl
  | cons e r ih =>
    have he := h e (List.mem_cons_self ..)
    simp only [List.map_cons, List.dropWhile_cons, he]
    split
    · exact ih fun e' m => h e' (List.mem_cons_of_mem _ m)
    · rfl

/-- `insertSorted` places the entry after the prefix released no later than it. -/
theorem insertSorted_eq_split (es : List (SeLe4n.SchedContextId × Nat)) (s : SeLe4n.SchedContextId)
    (t : Nat) : ReplenishQueue.insertSorted es s t =
      es.takeWhile (fun e => !decide (t < e.2)) ++ (s, t) :: es.dropWhile (fun e => !decide (t < e.2)) := by
  induction es with
  | nil => rfl
  | cons e r ih =>
    obtain ⟨id, tm⟩ := e
    unfold ReplenishQueue.insertSorted
    by_cases ht : t < tm
    · simp [ht]
    · simp [ht, ih]

/-- Linking in writes `s`'s link and its predecessor's successor; every other
context's link on every core is as it was. -/
theorem releaseLinkOn_releaseLinkIn (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) {sc : SchedContext} (hsc : st.getSchedContext? s = some sc)
    (hps : st.releasePredBefore c t (st.scheduler.releaseCountOnCore c) 0
        (st.scheduler.releaseHeadOnCore c) ≠ 0 →
      decode (st.releasePredBefore c t (st.scheduler.releaseCountOnCore c) 0
        (st.scheduler.releaseHeadOnCore c)) ≠ s)
    (c'' : CoreId) (y : SeLe4n.SchedContextId) :
    (st.releaseLinkIn c s t).releaseLinkOn c'' y =
      let p := st.releasePredBefore c t (st.scheduler.releaseCountOnCore c) 0
        (st.scheduler.releaseHeadOnCore c)
      let n := if p = 0 then st.scheduler.releaseHeadOnCore c else st.releaseNextOn c (decode p)
      if y = s then (if c'' = c then some (n, t) else none)
      else if p ≠ 0 ∧ y = decode p then
        (st.releaseLinkOn c'' y).map fun l => (code s, l.2)
      else st.releaseLinkOn c'' y := by
  unfold releaseLinkIn
  dsimp only
  rw [releaseLinkOn_withScheduler]
  generalize st.releasePredBefore c t (st.scheduler.releaseCountOnCore c) 0
    (st.scheduler.releaseHeadOnCore c) = p at hps ⊢
  generalize (if p = 0 then st.scheduler.releaseHeadOnCore c else st.releaseNextOn c (decode p)) = n
  have hS : (st.mapSchedContextInPlace s (SchedContext.joinRelease c n t)).releaseLinkOn c'' s =
      if c'' = c then some (n, t) else none := by
    rw [releaseLinkOn_mapSchedContextInPlace_self, hsc]
    simp [SchedContext.releaseLinkOn_joinRelease]
  by_cases hp : p = 0
  · simp only [hp, if_true, releaseLinkOn_withScheduler, ne_eq, not_true_eq_false, false_and,
      if_false]
    by_cases hy : y = s
    · subst hy; rw [hS, if_pos rfl]
    · rw [if_neg hy, releaseLinkOn_mapSchedContextInPlace_ne _ _ _ _ hy]
  · have hds := hps hp
    simp only [hp, if_false, ne_eq, not_false_eq_true, true_and]
    by_cases hy : y = s
    · subst hy
      rw [releaseLinkOn_mapSchedContextInPlace_ne _ _ _ _ (Ne.symm hds), hS, if_pos rfl]
    · rw [if_neg hy]
      by_cases hd : y = decode p
      · subst hd
        rw [if_pos rfl, releaseLinkOn_mapSchedContextInPlace_self,
          mapSchedContextInPlace_getSchedContext?_ne _ _ _ hy]
        unfold releaseLinkOn
        cases st.getSchedContext? (decode p) with
        | none => rfl
        | some sc => simp [SchedContext.releaseLinkOn_withReleaseNext]
      · rw [if_neg hd, releaseLinkOn_mapSchedContextInPlace_ne _ _ _ _ hd,
          releaseLinkOn_mapSchedContextInPlace_ne _ _ _ _ hy]

theorem releaseLinkIn_scheduler (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) (t : Nat) :
    (st.releaseLinkIn c s t).scheduler =
      (if st.releasePredBefore c t (st.scheduler.releaseCountOnCore c) 0
          (st.scheduler.releaseHeadOnCore c) = 0 then
        st.scheduler.setReleaseHeadOnCore c (code s)
      else st.scheduler).setReleaseCountOnCore c (st.scheduler.releaseCountOnCore c + 1) := by
  unfold releaseLinkIn
  dsimp only; split <;> rfl

theorem releaseLinkIn_replenishQueue (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) (t : Nat) :
    (st.releaseLinkIn c s t).scheduler.replenishQueue = st.scheduler.replenishQueue := by
  rw [releaseLinkIn_scheduler]; split <;> rfl

/-- A context its own fields place on no core is on no core's queue. -/
theorem releaseLinkOn_of_not_queuedAnywhere {st : SystemState} {s : SeLe4n.SchedContextId}
    (h : st.releaseQueuedAnywhere s = false) (c : CoreId) : st.releaseLinkOn c s = none := by
  unfold releaseQueuedAnywhere at h
  unfold releaseLinkOn
  cases e : st.getSchedContext? s with
  | none => rfl
  | some sc =>
    rw [e] at h
    unfold SchedContext.releaseLinkOn
    have hc := c.isLt
    have : ¬ sc.releaseCoreCode = c.val + 1 := by
      intro hcc; simp only [hcc] at h; simp at h; omega
    simp [this]

/-- The queued insert: `chain_insert` at the sorted place. -/
theorem releaseInsertOn_refined_of_fresh {st : SystemState} (h : st.releaseQueueRefined)
    (c : CoreId) (s : SeLe4n.SchedContextId) (t : Nat) {sc : SchedContext}
    (hsc : st.getSchedContext? s = some sc) (hfree : st.releaseQueuedAnywhere s = false)
    (c' : CoreId) : (st.releaseInsertFresh c s t).releaseQueueRefinedOnCore c' := by
  have hc := h c
  have hNone := releaseLinkOn_of_not_queuedAnywhere hfree
  generalize hes : (st.scheduler.replenishQueueOnCore c).entries = es at hc
  have hIds0 : st.releaseIds c = es.map Prod.fst := by simp only [releaseIds, hes]
  have hsI : s ∉ st.releaseIds c := fun m => by
    have := (hc.queued s).mpr m
    rw [releaseQueuedOn_eq, hNone c] at this; cases this
  have hTD := List.takeWhile_append_dropWhile (p := fun e : SeLe4n.SchedContextId × Nat =>
    !decide (t < e.2)) (l := es)
  generalize hA : (es.takeWhile fun e => !decide (t < e.2)).map Prod.fst = A
  generalize hB : (es.dropWhile fun e => !decide (t < e.2)).map Prod.fst = B
  have hIds : st.releaseIds c = A ++ B := by
    rw [hIds0, ← hA, ← hB, ← List.map_append, hTD]
  have hnd : (A ++ B).Nodup := hIds ▸ hc.nodup
  have hsAB : s ∉ A ++ B := hIds ▸ hsI
  have hchain : Chain (st.releaseNextOn c) (st.scheduler.releaseHeadOnCore c) (A ++ B) :=
    hIds ▸ hc.chain
  have hlen : (st.releaseIds c).length ≤ st.scheduler.releaseCountOnCore c := by
    rw [hc.count, hIds0, List.length_map, hes]; exact Nat.le_refl _
  have hAt : ∀ e ∈ es, st.releaseAtOn c e.1 = e.2 := fun e he => hc.at_eq e (hes ▸ he)
  have hp : st.releasePredBefore c t (st.scheduler.releaseCountOnCore c) 0
      (st.scheduler.releaseHeadOnCore c) = lastCode 0 A := by
    rw [releasePredBefore_eq, hc.chain.predBefore_eq _ t hlen 0, hIds0, ← hA]
    exact congrArg (lastCode 0) (map_fst_takeWhile hAt fun v => !decide (t < v))
  have hMemQ : ∀ y ∈ A ++ B, (st.releaseLinkOn c y).isSome = true := fun y hy => by
    rw [releaseLinkOn_isSome_iff_queued, hc.queued, hIds]; exact hy
  have hps : lastCode 0 A ≠ 0 → decode (lastCode 0 A) ≠ s := fun h0 e => by
    have hy := (lastCode_ne_zero_and_iff A s).mp ⟨h0, e.symm⟩
    exact hsAB (List.mem_append_left _ (List.mem_of_getLast? hy))
  have hn : (if lastCode 0 A = 0 then st.scheduler.releaseHeadOnCore c
      else st.releaseNextOn c (decode (lastCode 0 A))) = firstCode 0 B := by
    by_cases h0 : lastCode 0 A = 0
    · rw [if_pos h0, hchain.head_eq, (lastCode_zero_eq_zero_iff A).mp h0]; rfl
    · rw [if_neg h0]
      have hz := (lastCode_ne_zero_and_iff A _).mp ⟨h0, rfl⟩
      generalize decode (lastCode 0 A) = z at hz ⊢
      obtain ⟨A', rfl⟩ := List.getLast?_eq_some_iff.mp hz
      rw [List.append_assoc, List.singleton_append] at hchain
      exact hchain.next_eq
  have hLk : ∀ c'' y, (st.releaseLinkIn c s t).releaseLinkOn c'' y =
      if y = s then (if c'' = c then some (firstCode 0 B, t) else none)
      else if A.getLast? = some y then
        (st.releaseLinkOn c'' y).map fun l => (code s, l.2)
      else st.releaseLinkOn c'' y := fun c'' y => by
    have e := releaseLinkOn_releaseLinkIn st c s t hsc (by rw [hp]; exact hps) c'' y
    rw [hp] at e
    rw [e]; dsimp only
    rw [hn]
    by_cases hy : y = s
    · simp [hy]
    · rw [if_neg hy, if_neg hy]
      by_cases hl : A.getLast? = some y
      · rw [if_pos ((lastCode_ne_zero_and_iff A y).mpr hl), if_pos hl]
      · rw [if_neg (fun e => hl ((lastCode_ne_zero_and_iff A y).mp e)), if_neg hl]
  have hLk' : ∀ c'' y, (st.releaseInsertFresh c s t).releaseLinkOn c'' y =
      (st.releaseLinkIn c s t).releaseLinkOn c'' y := fun _ _ => rfl
  have hSch : (st.releaseInsertFresh c s t).scheduler = (st.releaseLinkIn c s t).scheduler.setReplenishQueueOnCore c
      ((st.scheduler.replenishQueueOnCore c).insert s t) := rfl
  have hLs := releaseLinkIn_scheduler st c s t
  rw [hp] at hLs
  have hHd : ∀ d, (st.releaseInsertFresh c s t).scheduler.releaseHeadOnCore d =
      if d = c ∧ lastCode 0 A = 0 then code s else st.scheduler.releaseHeadOnCore d := by
    intro d
    rw [hSch, SchedulerState.setReplenishQueueOnCore_releaseHeadOnCore, hLs,
      SchedulerState.setReleaseCountOnCore_releaseHeadOnCore']
    by_cases h0 : lastCode 0 A = 0
    · rw [if_pos h0]
      by_cases hd : d = c
      · subst hd; simp [h0]
      · rw [SchedulerState.setReleaseHeadOnCore_releaseHeadOnCore_ne _ _ _ _ (Ne.symm hd)]; simp [hd]
    · rw [if_neg h0]; simp [h0]
  have hCt : ∀ d, (st.releaseInsertFresh c s t).scheduler.releaseCountOnCore d =
      if d = c then st.scheduler.releaseCountOnCore c + 1 else st.scheduler.releaseCountOnCore d := by
    intro d
    rw [hSch, SchedulerState.setReplenishQueueOnCore_releaseCountOnCore, hLs]
    by_cases hd : d = c
    · subst hd; simp
    · rw [if_neg hd, SchedulerState.setReleaseCountOnCore_releaseCountOnCore_ne _ _ _ _ (Ne.symm hd)]
      split <;> simp
  rcases Decidable.em (c' = c) with rfl | hne
  · have hQ' : ((st.releaseInsertFresh c' s t).scheduler.replenishQueueOnCore c').entries =
        es.takeWhile (fun e => !decide (t < e.2)) ++ (s, t) :: es.dropWhile (fun e => !decide (t < e.2)) := by
      rw [hSch, SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self]
      show ReplenishQueue.insertSorted _ _ _ = _
      rw [hes]; exact insertSorted_eq_split es s t
    have hIds' : (st.releaseInsertFresh c' s t).releaseIds c' = A ++ s :: B := by
      unfold releaseIds; rw [hQ', List.map_append, List.map_cons, hA, hB]
    have hne_s : ∀ z ∈ A ++ B, z ≠ s := fun z hz e => hsAB (e ▸ hz)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hIds']
      have hI := chain_insert (nx' := (st.releaseInsertFresh c' s t).releaseNextOn c') (y := s)
        hchain hnd
        (fun z hz hzl => by
          rw [releaseNextOn_eq, releaseNextOn_eq, hLk', hLk, if_neg (hne_s z hz), if_neg hzl])
        (fun z hz => by
          have hzA := List.mem_of_getLast? hz
          rw [releaseNextOn_eq, hLk', hLk, if_neg (hne_s z (List.mem_append_left _ hzA)), if_pos hz,
            nextOfLinks_map_some (hMemQ z (List.mem_append_left _ hzA))])
        (by rw [releaseNextOn_eq, hLk', hLk, if_pos rfl, if_pos rfl])
      have hH : (st.releaseInsertFresh c' s t).scheduler.releaseHeadOnCore c' =
          firstCode (code s) A := by
        rw [hHd]
        by_cases h0 : lastCode 0 A = 0
        · rw [if_pos ⟨rfl, h0⟩, (lastCode_zero_eq_zero_iff A).mp h0]; rfl
        · rw [if_neg (fun e => h0 e.2), hchain.head_eq]
          have hAne : A ≠ [] := fun e => h0 ((lastCode_zero_eq_zero_iff A).mpr e)
          cases A with
          | nil => exact absurd rfl hAne
          | cons x r => rfl
      rw [hH]; exact hI
    · rw [hIds']
      exact List.perm_middle.nodup_iff.mpr (List.nodup_cons.mpr ⟨hsAB, hnd⟩)
    · intro y
      rw [releaseQueuedOn_eq, hLk', hLk, hIds']
      by_cases hy : y = s
      · subst hy; simp
      · rw [if_neg hy]
        have hiff : (st.releaseLinkOn c' y).isSome = true ↔ y ∈ A ++ s :: B := by
          rw [releaseLinkOn_isSome_iff_queued, hc.queued, hIds]; simp [hy]
        split
        · rw [Option.isSome_map]; exact hiff
        · exact hiff
    · intro e he
      rw [hQ'] at he
      rw [releaseAtOn_eq, hLk', hLk]
      by_cases hmem : e ∈ es
      · have he1 : e.1 ∈ A ++ B := by
          rw [← hIds, hIds0]; exact List.mem_map_of_mem hmem
        have hold := hAt e hmem
        rw [releaseAtOn_eq] at hold
        rw [if_neg (hne_s _ he1)]
        by_cases hl : A.getLast? = some e.1
        · rw [if_pos hl]
          rcases hL : st.releaseLinkOn c' e.1 with _ | ⟨n, a⟩ <;> rw [hL] at hold <;> simpa using hold
        · rw [if_neg hl]; exact hold
      · have hst : e = (s, t) := by
          simp only [List.mem_append, List.mem_cons] at he
          rcases he with he | he | he
          · exact absurd ((List.takeWhile_sublist _).subset he) hmem
          · exact he
          · exact absurd ((List.dropWhile_sublist _).subset he) hmem
        subst hst; simp
    · rw [hCt, if_pos rfl, hQ', hc.count, hes]
      have hl := congrArg List.length hTD
      simp only [List.length_append] at hl
      simp only [List.length_append, List.length_cons]; omega
  · have hLc : ∀ y, (st.releaseInsertFresh c s t).releaseLinkOn c' y = st.releaseLinkOn c' y := by
      intro y
      rw [hLk', hLk]
      by_cases hy : y = s
      · subst hy; rw [if_pos rfl, if_neg hne, hNone]
      · rw [if_neg hy]
        split
        · rename_i hl
          rw [releaseLinkOn_ne_core hne (hMemQ y (List.mem_append_left _ (List.mem_of_getLast? hl)))]; rfl
        · rfl
    refine releaseQueueRefinedOnCore_of_frame hLc ?_ ?_ ?_ (h c')
    · rw [hSch, SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ (Ne.symm hne)]
      unfold SchedulerState.replenishQueueOnCore; rw [releaseLinkIn_replenishQueue]
    · rw [hHd]; simp [hne]
    · rw [hCt]; simp [hne]

/-- **Queueing a context keeps every core's agreement.** -/
theorem releaseInsertOn_refined {st : SystemState} (h : st.releaseQueueRefined) (c : CoreId)
    (s : SeLe4n.SchedContextId) (t : Nat) : (st.releaseInsertOn c s t).releaseQueueRefined := by
  unfold releaseInsertOn
  split
  · exact h
  · rename_i hg
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, Option.isNone_iff_eq_none] at hg
    obtain ⟨hfree, hsc⟩ := hg
    obtain ⟨sc, hsc⟩ := Option.ne_none_iff_exists'.mp hsc
    exact releaseInsertOn_refined_of_fresh h c s t hsc hfree

/-! ## The queue's entries read along the links -/

/-- WS-ZA ZA6.3: core `c`'s release queue as entries, read along the links:
each context with the release time its link holds.  Builds a list, so it is
for boot-time and test readers (the freeze, the suites), not a kernel entry. -/
def releaseEntriesOn (st : SystemState) (c : CoreId) : List (SeLe4n.SchedContextId × Nat) :=
  (st.releaseWalk c (st.scheduler.releaseCountOnCore c) (st.scheduler.releaseHeadOnCore c)).map
    fun s => (s, st.releaseAtOn c s)

theorem map_pair_of_snd_eq {es : List (SeLe4n.SchedContextId × Nat)} {tm : SeLe4n.SchedContextId → Nat}
    (h : ∀ e ∈ es, tm e.1 = e.2) : (es.map Prod.fst).map (fun s => (s, tm s)) = es := by
  induction es with
  | nil => rfl
  | cons e r ih =>
    simp only [List.map_cons, h e (List.mem_cons_self ..)]
    rw [ih fun e' m => h e' (List.mem_cons_of_mem _ m)]

/-- **The entries read along the links are the abstract queue's.** -/
theorem releaseEntriesOn_eq {st : SystemState} (h : st.releaseQueueRefined) (c : CoreId) :
    st.releaseEntriesOn c = (st.scheduler.replenishQueueOnCore c).entries := by
  have hc := h c
  have hlen : (st.releaseIds c).length ≤ st.scheduler.releaseCountOnCore c := by
    rw [hc.count, List.length_map]; exact Nat.le_refl _
  unfold releaseEntriesOn
  rw [releaseWalk_eq, hc.chain.walk_eq hlen]
  exact map_pair_of_snd_eq hc.at_eq

/-! ## The edits write the release fields alone -/

theorem releaseUnlinkOn_agree (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    objectsAgreeOffReleaseLinks (st.releaseUnlinkOn c s) st := by
  have h1 := objectsAgreeOffReleaseLinks.mapSchedContextInPlace st s SchedContext.leaveRelease
    fun _ => rfl
  unfold releaseUnlinkOn
  by_cases hq : st.releaseQueuedOn c s = true
  · rw [if_pos hq]
    by_cases hp : st.releasePredOf c s (st.scheduler.releaseCountOnCore c) 0
        (st.scheduler.releaseHeadOnCore c) = 0
    · exact objectsAgreeOffReleaseLinks.congr (by simp only [hp, if_true]) h1
    · exact objectsAgreeOffReleaseLinks.congr (by simp only [hp, if_false])
        ((objectsAgreeOffReleaseLinks.mapSchedContextInPlace
          (st.mapSchedContextInPlace s SchedContext.leaveRelease)
          (decode (st.releasePredOf c s (st.scheduler.releaseCountOnCore c) 0
            (st.scheduler.releaseHeadOnCore c)))
          (SchedContext.withReleaseNext (st.releaseNextOn c s)) fun _ => rfl).trans h1)
  · rw [if_neg hq]; exact .refl _

theorem releaseRemoveOn_agree (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    objectsAgreeOffReleaseLinks (st.releaseRemoveOn c s) st :=
  objectsAgreeOffReleaseLinks.congr rfl (releaseUnlinkOn_agree st c s)

theorem releaseLinkIn_agree (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) (t : Nat) :
    objectsAgreeOffReleaseLinks (st.releaseLinkIn c s t) st := by
  unfold releaseLinkIn
  dsimp only
  generalize st.releasePredBefore c t (st.scheduler.releaseCountOnCore c) 0
    (st.scheduler.releaseHeadOnCore c) = p
  generalize (if p = 0 then st.scheduler.releaseHeadOnCore c else st.releaseNextOn c (decode p)) = n
  have h1 := objectsAgreeOffReleaseLinks.mapSchedContextInPlace st s
    (SchedContext.joinRelease c n t) fun _ => rfl
  by_cases hp : p = 0
  · exact objectsAgreeOffReleaseLinks.congr (by simp only [hp, if_true]) h1
  · exact objectsAgreeOffReleaseLinks.congr (by simp only [hp, if_false])
      ((objectsAgreeOffReleaseLinks.mapSchedContextInPlace
        (st.mapSchedContextInPlace s (SchedContext.joinRelease c n t)) (decode p)
        (SchedContext.withReleaseNext (code s)) fun _ => rfl).trans h1)

theorem releaseInsertOn_agree (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) (t : Nat) :
    objectsAgreeOffReleaseLinks (st.releaseInsertOn c s t) st := by
  unfold releaseInsertOn
  split
  · exact .refl _
  · exact objectsAgreeOffReleaseLinks.congr rfl (releaseLinkIn_agree st c s t)

/-! ## Removing a context from whichever queue holds it -/

/-- The core whose release queue a context's link names, read from the
context alone. -/
@[inline] def _root_.SeLe4n.Kernel.SchedContext.releaseCore? (sc : SchedContext) : Option CoreId :=
  if h : sc.releaseCoreCode ≠ 0 ∧ sc.releaseCoreCode ≤ Concurrency.numCores then
    some ⟨sc.releaseCoreCode - 1, by omega⟩
  else none

theorem _root_.SeLe4n.Kernel.SchedContext.releaseCore?_eq_some_iff (sc : SchedContext) (d : CoreId) :
    sc.releaseCore? = some d ↔ sc.releaseCoreCode = d.val + 1 := by
  unfold SchedContext.releaseCore?
  have hd := d.isLt
  constructor
  · intro e
    split at e
    · cases e; simp only; omega
    · cases e
  · intro e
    rw [dif_pos (by omega)]
    congr 1; apply Fin.ext; simp only; omega

theorem _root_.SeLe4n.Kernel.SchedContext.releaseCore?_eq_none_iff (sc : SchedContext) :
    sc.releaseCore? = none ↔ ∀ d : CoreId, sc.releaseCoreCode ≠ d.val + 1 := by
  constructor
  · intro e d hd
    rw [(sc.releaseCore?_eq_some_iff d).mpr hd] at e; cases e
  · intro hn
    cases e : sc.releaseCore? with
    | none => rfl
    | some d => exact absurd ((sc.releaseCore?_eq_some_iff d).mp e) (hn d)


/-- A transition that leaves every release link, every head, every count and
every abstract queue's entries as they were keeps the agreement. -/
theorem releaseQueueRefined_of_entries {st st' : SystemState} (hL : ReleaseLinksAgree st' st)
    (hE : ∀ c, (st'.scheduler.replenishQueueOnCore c).entries = (st.scheduler.replenishQueueOnCore c).entries)
    (hH : st'.scheduler.releaseHeadCode = st.scheduler.releaseHeadCode)
    (hC : st'.scheduler.releaseCount = st.scheduler.releaseCount)
    (h : st.releaseQueueRefined) : st'.releaseQueueRefined := by
  intro c
  have hc := h c
  have hHd : st'.scheduler.releaseHeadOnCore c = st.scheduler.releaseHeadOnCore c := by
    unfold SchedulerState.releaseHeadOnCore; rw [hH]
  have hCt : st'.scheduler.releaseCountOnCore c = st.scheduler.releaseCountOnCore c := by
    unfold SchedulerState.releaseCountOnCore; rw [hC]
  have hIds : st'.releaseIds c = st.releaseIds c := by unfold releaseIds; rw [hE]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hL.nextOn c, hHd, hIds]; exact hc.chain
  · rw [hIds]; exact hc.nodup
  · intro s; rw [hL.queuedOn c, hIds]; exact hc.queued s
  · intro e he; rw [hL.atOn c]; rw [hE] at he; exact hc.at_eq e he
  · rw [hCt, hE]; exact hc.count

/-- The core whose release queue context `s`'s own link names, if any. -/
def releaseCoreOf (st : SystemState) (s : SeLe4n.SchedContextId) : Option CoreId :=
  (st.getSchedContext? s).bind SchedContext.releaseCore?

/-- WS-ZA ZA6.3: take context `s` off the release queue its own link names —
exact, whichever core that is, with no core computed for it: the links and that
core's abstract queue, nothing on any other core.  A context on no queue, or no
context, is left as it is. -/
def releaseRemoveAnywhere (st : SystemState) (s : SeLe4n.SchedContextId) : SystemState :=
  match st.releaseCoreOf s with
  | some d => st.releaseRemoveOn d s
  | none => st

theorem releaseRemoveAnywhere_agree (st : SystemState) (s : SeLe4n.SchedContextId) :
    objectsAgreeOffReleaseLinks (st.releaseRemoveAnywhere s) st := by
  unfold releaseRemoveAnywhere
  split
  · exact releaseRemoveOn_agree _ _ _
  · exact .refl _

theorem releaseRemoveAnywhere_refined {st : SystemState} (h : st.releaseQueueRefined)
    (s : SeLe4n.SchedContextId) : (st.releaseRemoveAnywhere s).releaseQueueRefined := by
  unfold releaseRemoveAnywhere
  split
  · exact releaseRemoveOn_refined h _ _
  · exact h

/-- A context is on no queue exactly when it holds no link on any core. -/
theorem releaseQueuedAnywhere_eq_false_iff (st : SystemState) (s : SeLe4n.SchedContextId) :
    st.releaseQueuedAnywhere s = false ↔ ∀ c, st.releaseLinkOn c s = none := by
  unfold releaseQueuedAnywhere releaseLinkOn
  cases e : st.getSchedContext? s with
  | none => simp
  | some sc =>
    simp only
    unfold SchedContext.releaseLinkOn
    constructor
    · intro h c
      have hc := c.isLt
      have : ¬ sc.releaseCoreCode = c.val + 1 := by
        intro hcc; simp only [hcc] at h; simp at h; omega
      simp [this]
    · intro h
      cases hb : (sc.releaseCoreCode != 0 && decide (sc.releaseCoreCode ≤ Concurrency.numCores)) with
      | false => rfl
      | true =>
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hb
        have := h ⟨sc.releaseCoreCode - 1, by omega⟩
        simp only at this
        rw [if_pos (by omega)] at this
        cases this

/-- The link a context's core code names is the one it is queued on. -/
theorem releaseQueuedOn_of_releaseCoreOf {st : SystemState} {s : SeLe4n.SchedContextId}
    {d : CoreId} (e : st.releaseCoreOf s = some d) : st.releaseQueuedOn d s = true := by
  rw [releaseQueuedOn_eq]
  unfold releaseLinkOn
  unfold releaseCoreOf at e
  cases e' : st.getSchedContext? s with
  | none => rw [e'] at e; cases e
  | some sc =>
    rw [e'] at e
    simp only [Option.bind_some] at e
    simp [SchedContext.releaseLinkOn, (sc.releaseCore?_eq_some_iff d).mp e]

/-- A context whose core code names no core holds no link. -/
theorem releaseLinkOn_of_releaseCoreOf_none {st : SystemState} {s : SeLe4n.SchedContextId}
    (e : st.releaseCoreOf s = none) (c : CoreId) : st.releaseLinkOn c s = none := by
  unfold releaseLinkOn
  unfold releaseCoreOf at e
  cases e' : st.getSchedContext? s with
  | none => rfl
  | some sc =>
    rw [e'] at e
    simp only [Option.bind_some] at e
    unfold SchedContext.releaseLinkOn
    simp only [if_neg ((sc.releaseCore?_eq_none_iff).mp e c)]

/-- **After the removal the context is on no queue.** -/
theorem releaseRemoveAnywhere_not_queued (st : SystemState) (s : SeLe4n.SchedContextId) :
    (st.releaseRemoveAnywhere s).releaseQueuedAnywhere s = false := by
  rw [releaseQueuedAnywhere_eq_false_iff]
  intro c
  unfold releaseRemoveAnywhere
  cases e : st.releaseCoreOf s with
  | some d =>
    show (st.releaseUnlinkOn d s).releaseLinkOn c s = none
    rw [releaseLinkOn_releaseUnlinkOn st d s (releaseQueuedOn_of_releaseCoreOf e)]; simp
  | none => exact releaseLinkOn_of_releaseCoreOf_none e c

/-! ## A context's place: its pending head refill -/

/-- WS-ZA ZA6.4: where a context goes on its release queue: the release time of
its first pending refill while its head is used up, as seL4-MCS keys the release
queue by the head refill's `rTime` of a context whose head is not yet ready
(`refill_ready`); none while its head holds budget or it holds no refill.  The
context's fields are read directly, so no refill list is built. -/
@[inline] def _root_.SeLe4n.Kernel.SchedContext.releaseKey? (sc : SchedContext) : Option Nat :=
  if sc.budgetRemaining.val = 0 ∧ sc.refillHeadPresent = true then some sc.refillHeadEligibleAt
  else none

/-- The place read as seL4-MCS states it: the first pending refill's release
time, while the head is used up. -/
theorem _root_.SeLe4n.Kernel.SchedContext.releaseKey?_eq_head (sc : SchedContext) :
    sc.releaseKey? =
      if sc.budgetRemaining.val = 0 then sc.replenishments.head?.map (·.eligibleAt) else none := by
  unfold SchedContext.releaseKey? SchedContext.replenishments
  by_cases hB : sc.budgetRemaining.val = 0 <;> cases hP : sc.refillHeadPresent <;> simp [hB]

theorem _root_.SeLe4n.Kernel.SchedContext.releaseKey?_eq_some {sc : SchedContext} {t : Nat} :
    sc.releaseKey? = some t ↔
      sc.budgetRemaining.val = 0 ∧ sc.refillHeadPresent = true ∧ sc.refillHeadEligibleAt = t := by
  unfold SchedContext.releaseKey?
  split <;> simp_all

/-- WS-ZA ZA6.3: core `c`'s release queue as the abstract queue reads it holds
each context at its place: a queued context is held by the store and its
entry's time is its place (`releaseKey?`). -/
def releaseQueueKeyed (st : SystemState) : Prop :=
  ∀ c e, e ∈ (st.scheduler.replenishQueueOnCore c).entries →
    ∃ sc, st.getSchedContext? e.1 = some sc ∧ sc.releaseKey? = some e.2

/-- A context's place, read from the store. -/
def releaseKeyOf (st : SystemState) (s : SeLe4n.SchedContextId) : Option Nat :=
  (st.getSchedContext? s).bind SchedContext.releaseKey?

theorem releaseKeyOf_eq_some {st : SystemState} {s : SeLe4n.SchedContextId} {t : Nat} :
    st.releaseKeyOf s = some t ↔ ∃ sc, st.getSchedContext? s = some sc ∧ sc.releaseKey? = some t := by
  unfold releaseKeyOf
  cases st.getSchedContext? s <;> simp

/-- A write to the release fields alone keeps every context's place. -/
theorem objectsAgreeOffReleaseLinks.releaseKeyOf {st st' : SystemState}
    (h : objectsAgreeOffReleaseLinks st' st) (s : SeLe4n.SchedContextId) :
    st'.releaseKeyOf s = st.releaseKeyOf s := by
  have hr := h.getSchedContext?_map SchedContext.releaseKey? (fun _ => rfl) s
  unfold SystemState.releaseKeyOf
  cases e : st.getSchedContext? s <;> cases e' : st'.getSchedContext? s <;> rw [e, e'] at hr <;>
    simp_all

/-- **The keying survives any step whose entries are old entries or the one
new entry at its context's place**, and whose context writes are to the
release fields alone. -/
theorem releaseQueueKeyed_of {st st' : SystemState} (h : st.releaseQueueKeyed)
    (hA : objectsAgreeOffReleaseLinks st' st)
    (hE : ∀ c e, e ∈ (st'.scheduler.replenishQueueOnCore c).entries →
      e ∈ (st.scheduler.replenishQueueOnCore c).entries ∨ st'.releaseKeyOf e.1 = some e.2) :
    st'.releaseQueueKeyed := by
  intro c e he
  rw [← releaseKeyOf_eq_some]
  rcases hE c e he with hm | hk
  · rw [hA.releaseKeyOf]; exact releaseKeyOf_eq_some.mpr (h c e hm)
  · exact hk

/-! ## What the edits write to the abstract queue -/

theorem releaseRemoveOn_replenishQueueOnCore (st : SystemState) (c : CoreId)
    (s : SeLe4n.SchedContextId) (c' : CoreId) :
    (st.releaseRemoveOn c s).scheduler.replenishQueueOnCore c' =
      if c' = c then (st.scheduler.replenishQueueOnCore c).remove s
      else st.scheduler.replenishQueueOnCore c' := by
  show ((st.releaseUnlinkOn c s).scheduler.setReplenishQueueOnCore c _).replenishQueueOnCore c' = _
  by_cases h : c' = c
  · subst h; rw [if_pos rfl, SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self]
  · rw [if_neg h, SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ (Ne.symm h)]
    unfold SchedulerState.replenishQueueOnCore; rw [releaseUnlinkOn_replenishQueue]

theorem releaseInsertFresh_replenishQueueOnCore (st : SystemState) (c : CoreId)
    (s : SeLe4n.SchedContextId) (t : Nat) (c' : CoreId) :
    (st.releaseInsertFresh c s t).scheduler.replenishQueueOnCore c' =
      if c' = c then (st.scheduler.replenishQueueOnCore c).insert s t
      else st.scheduler.replenishQueueOnCore c' := by
  show ((st.releaseLinkIn c s t).scheduler.setReplenishQueueOnCore c _).replenishQueueOnCore c' = _
  by_cases h : c' = c
  · subst h; rw [if_pos rfl, SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self]
  · rw [if_neg h, SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ (Ne.symm h)]
    unfold SchedulerState.replenishQueueOnCore; rw [releaseLinkIn_replenishQueue]

/-- A context queued on core `c` names `c` by its own core code. -/
theorem releaseCoreOf_of_queuedOn {st : SystemState} {c : CoreId} {s : SeLe4n.SchedContextId}
    (hq : st.releaseQueuedOn c s = true) : st.releaseCoreOf s = some c := by
  unfold releaseQueuedOn at hq
  unfold releaseCoreOf
  cases e : st.getSchedContext? s with
  | none => rw [e] at hq; cases hq
  | some sc =>
    rw [e] at hq
    simp only [Option.bind_some]
    exact (sc.releaseCore?_eq_some_iff c).mpr (by simpa using hq)

/-- A context update that keeps the core code keeps every context's link core. -/
theorem releaseCoreOf_updateSchedContext (st : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hInv : st.objects.invExt)
    (hf : ∀ sc, (f sc).releaseCoreCode = sc.releaseCoreCode) (s : SeLe4n.SchedContextId) :
    (st.updateSchedContext scId f).releaseCoreOf s = st.releaseCoreOf s := by
  unfold releaseCoreOf
  by_cases hs : s = scId
  · subst hs
    rw [updateSchedContext_getSchedContext?_self _ _ _ hInv]
    cases st.getSchedContext? s with
    | none => rfl
    | some sc => simp only [Option.map_some, Option.bind_some, SchedContext.releaseCore?, hf]
  · rw [updateSchedContext_getSchedContext?_ne _ _ _ hInv _
      (fun h => hs (SeLe4n.SchedContextId.toObjId_injective _ _ h).symm)]

/-- A context rewrite that keeps the core code keeps every context's link core. -/
theorem releaseCoreOf_rewriteObject_schedContext (st : SystemState) (scId : SeLe4n.SchedContextId)
    (sc sc' : SchedContext) (hsc : st.getSchedContext? scId = some sc)
    {h : st.rewriteAdmissible scId.toObjId (.schedContext sc')} (hInv : st.objects.invExt)
    (hf : sc'.releaseCoreCode = sc.releaseCoreCode) (s : SeLe4n.SchedContextId) :
    (st.rewriteObject scId.toObjId (.schedContext sc') h).releaseCoreOf s = st.releaseCoreOf s := by
  unfold releaseCoreOf
  by_cases hs : s = scId
  · subst hs
    have e : (st.rewriteObject s.toObjId (.schedContext sc') h).getSchedContext? s = some sc' := by
      unfold getSchedContext?; rw [rewriteObject_objects_self _ _ _ _ hInv]
    rw [e, hsc]
    simp only [Option.bind_some, SchedContext.releaseCore?, hf]
  · rw [rewriteObject_getSchedContext?_ne _ _ _ _ hInv _
      (fun h => hs (SeLe4n.SchedContextId.toObjId_injective _ _ h).symm)]

/-- …and so does the same write spelled as a bare insert. -/
theorem releaseCoreOf_insert_schedContext (st : SystemState) (scId : SeLe4n.SchedContextId)
    (sc sc' : SchedContext) (hsc : st.getSchedContext? scId = some sc) (hInv : st.objects.invExt)
    (hf : sc'.releaseCoreCode = sc.releaseCoreCode) (s : SeLe4n.SchedContextId) :
    ({ st with objects := st.objects.insert scId.toObjId (.schedContext sc') } : SystemState).releaseCoreOf s =
      st.releaseCoreOf s :=
  releaseCoreOf_rewriteObject_schedContext st scId sc sc' hsc
    (h := rewriteAdmissible_schedContext hsc sc') hInv hf s

/-- A thread write moves no context's release link. -/
theorem releaseCoreOf_updateTcb (st : SystemState) (tid : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt) (s : SeLe4n.SchedContextId) :
    (st.updateTcb tid f).releaseCoreOf s = st.releaseCoreOf s := by
  unfold releaseCoreOf; rw [updateTcb_getSchedContext? _ _ _ hInv]

/-- The release-link-keeping context rewrite, over a stage holding the
pre-state's objects (a scheduler-only update of it). -/
theorem releaseCoreOf_rewrite_of_objects (S0 st : SystemState) (hO : S0.objects = st.objects)
    (x : SeLe4n.ObjId) (k : SeLe4n.SchedContextId) (hk : k.toObjId = x) (sc sc' : SchedContext)
    (hSc : st.getSchedContext? k = some sc) (hInv : st.objects.invExt)
    (hf : sc'.releaseCoreCode = sc.releaseCoreCode) (h : S0.rewriteAdmissible x (.schedContext sc'))
    (s : SeLe4n.SchedContextId) :
    (S0.rewriteObject x (.schedContext sc') h).releaseCoreOf s = st.releaseCoreOf s := by
  subst hk
  have hSc0 : S0.getSchedContext? k = some sc := by
    unfold getSchedContext? at *; rw [hO]; exact hSc
  rw [releaseCoreOf_rewriteObject_schedContext S0 k sc sc' hSc0 (by rw [hO]; exact hInv) hf s]
  unfold releaseCoreOf getSchedContext?; rw [hO]

/-- **The removal writes the abstract queue of the core the context's own link
names, and no other.** -/
theorem releaseRemoveAnywhere_replenishQueueOnCore (st : SystemState) (s : SeLe4n.SchedContextId)
    (c : CoreId) :
    (st.releaseRemoveAnywhere s).scheduler.replenishQueueOnCore c =
      if st.releaseCoreOf s = some c then (st.scheduler.replenishQueueOnCore c).remove s
      else st.scheduler.replenishQueueOnCore c := by
  cases e : st.releaseCoreOf s with
  | none =>
    rw [show st.releaseRemoveAnywhere s = st by unfold releaseRemoveAnywhere; rw [e]]; simp
  | some d =>
    rw [show st.releaseRemoveAnywhere s = st.releaseRemoveOn d s by unfold releaseRemoveAnywhere; rw [e]]
    simp only [Option.some.injEq]
    rw [releaseRemoveOn_replenishQueueOnCore]
    by_cases h : c = d
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]

/-- The removal leaves every core its link does not name as it was. -/
theorem releaseRemoveAnywhere_replenishQueueOnCore_ne (st : SystemState)
    (s : SeLe4n.SchedContextId) (c : CoreId) (h : st.releaseCoreOf s ≠ some c) :
    (st.releaseRemoveAnywhere s).scheduler.replenishQueueOnCore c =
      st.scheduler.replenishQueueOnCore c := by
  rw [releaseRemoveAnywhere_replenishQueueOnCore, if_neg h]

/-- The entries a removal keeps. -/
abbrev dropEntriesOf (s : SeLe4n.SchedContextId) (es : List (SeLe4n.SchedContextId × Nat)) :
    List (SeLe4n.SchedContextId × Nat) :=
  es.filter (fun (id, _) => !(id == s))

/-- **Over agreeing queues the removal drops the context's entry from every
core's abstract queue**: the one its link names is filtered, and no other holds
one. -/
theorem releaseRemoveAnywhere_entries {st : SystemState} (h : st.releaseQueueRefined)
    (s : SeLe4n.SchedContextId) (c : CoreId) :
    ((st.releaseRemoveAnywhere s).scheduler.replenishQueueOnCore c).entries =
      dropEntriesOf s (st.scheduler.replenishQueueOnCore c).entries := by
  rw [releaseRemoveAnywhere_replenishQueueOnCore]
  split
  · rfl
  · rename_i hne
    exact (filter_ne_of_not_mem fun m =>
      hne (releaseCoreOf_of_queuedOn (((h c).queued s).mpr m))).symm

/-- A removal only ever drops entries. -/
theorem releaseRemoveAnywhere_entries_subset (st : SystemState) (s : SeLe4n.SchedContextId)
    (c' : CoreId) (e : SeLe4n.SchedContextId × Nat)
    (he : e ∈ ((st.releaseRemoveAnywhere s).scheduler.replenishQueueOnCore c').entries) :
    e ∈ (st.scheduler.replenishQueueOnCore c').entries := by
  rw [releaseRemoveAnywhere_replenishQueueOnCore] at he
  split at he
  · exact (List.mem_filter.mp he).1
  · exact he

/-- An entry naming the removed context survives only on a core its link did
not name. -/
theorem releaseRemoveAnywhere_entries_self (st : SystemState) (s : SeLe4n.SchedContextId)
    (c : CoreId) (e : SeLe4n.SchedContextId × Nat)
    (he : e ∈ ((st.releaseRemoveAnywhere s).scheduler.replenishQueueOnCore c).entries)
    (hs : e.1 = s) : st.releaseCoreOf s ≠ some c := by
  intro hc
  rw [releaseRemoveAnywhere_replenishQueueOnCore, if_pos hc] at he
  have := (List.mem_filter.mp he).2
  simp [hs] at this

/-- Removing a context's entries twice is removing them once. -/
theorem _root_.SeLe4n.Kernel.ReplenishQueue.remove_remove (rq : ReplenishQueue)
    (s : SeLe4n.SchedContextId) : (rq.remove s).remove s = rq.remove s := by
  simp only [ReplenishQueue.remove, List.filter_filter, Bool.and_self]

/-! ## Placing a context by its refills -/

/-- Is core `c` free to queue context `s`: its own link names `c`, or no core.
A context linked on another core's queue holds its one set of link fields there,
so it cannot also be linked on `c`'s. -/
@[inline] def releaseFreeFor (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) : Bool :=
  match st.releaseCoreOf s with
  | some d => d == c
  | none => true

theorem releaseFreeFor_iff (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    st.releaseFreeFor c s = true ↔ ∀ d, st.releaseCoreOf s = some d → d = c := by
  unfold releaseFreeFor
  cases st.releaseCoreOf s with
  | none => simp
  | some d => simp

/-- WS-ZA ZA6.3: put context `s` where its refills say, on core `c`'s release
queue: off `c`'s queue, then linked in at its place (`releaseKey?`: its first
pending refill's release time while its head is used up) — or left off it when it
has none.  seL4-MCS's `postpone` and the release
queue's re-placement after `awaken` in one write.  It writes core `c`'s queue
alone, the one whose lock the caller holds; a context linked on another core's
queue is left as it is (`releaseFreeFor`), and no caller hands it one. -/
def releasePlace (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) : SystemState :=
  if st.releaseFreeFor c s then
    match st.releaseKeyOf s with
    | some t => (st.releaseRemoveOn c s).releaseInsertOn c s t
    | none => st.releaseRemoveOn c s
  else st

/-- WS-ZA ZA6.3: `releasePlace`'s writes for a context placed at `t`: a call, so the place is read off the context before the
context's links are written, and the context's cell is not held across them. -/
@[noinline] def releaseReplace (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) : SystemState :=
  (st.releaseRemoveOn c s).releaseInsertOn c s t

/-- WS-ZA ZA6.3: the compiled `releasePlace`.  The context is read once: its
link's core compared as a number and its place read from its refill fields
(`releaseKey?`), then the writes are one call.  The specification reads the
core and the place as options (`releaseCoreOf`, `releaseKeyOf`), each built
when the store shares the context's entry.  Proven equal
(`releasePlace_eq_impl`). -/
def releasePlaceImpl (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) : SystemState :=
  match st.getSchedContext? s with
  | some sc =>
    if sc.releaseCoreCode == 0 || decide (Concurrency.numCores < sc.releaseCoreCode) ||
        sc.releaseCoreCode == c.val + 1 then
      if sc.budgetRemaining.val == 0 && sc.refillHeadPresent then
        st.releaseReplace c s sc.refillHeadEligibleAt
      else st.releaseRemoveOn c s
    else st
  | none => st.releaseRemoveOn c s

theorem releaseCore?_beq_eq (sc : SchedContext) (c : CoreId) :
    (match sc.releaseCore? with | some d => d == c | none => true) =
      (sc.releaseCoreCode == 0 || decide (Concurrency.numCores < sc.releaseCoreCode) ||
        sc.releaseCoreCode == c.val + 1) := by
  have hc := c.isLt
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  cases e : sc.releaseCore? with
  | some d =>
    have hd := (sc.releaseCore?_eq_some_iff d).mp e
    have hdl := d.isLt
    simp only [beq_iff_eq, Fin.ext_iff]
    omega
  | none =>
    have hn := (sc.releaseCore?_eq_none_iff).mp e
    simp only [true_iff]
    by_cases h0 : sc.releaseCoreCode = 0
    · exact Or.inl (Or.inl h0)
    · by_cases hl : Concurrency.numCores < sc.releaseCoreCode
      · exact Or.inl (Or.inr hl)
      · exact absurd rfl (hn ⟨sc.releaseCoreCode - 1, by omega⟩ |> fun h => fun _ => h (by simp only; omega))

@[csimp] theorem releasePlace_eq_impl : @releasePlace = @releasePlaceImpl := by
  funext st c s
  unfold releasePlace releasePlaceImpl releaseReplace releaseFreeFor releaseKeyOf releaseCoreOf
  cases st.getSchedContext? s with
  | none => rfl
  | some sc =>
    simp only [Option.bind_some]
    rw [releaseCore?_beq_eq]
    unfold SchedContext.releaseKey?
    split
    · by_cases hB : sc.budgetRemaining.val = 0 <;> by_cases hP : sc.refillHeadPresent = true <;>
        simp [hB, hP]
    · rfl

/-! ## The edits keep the object table's invariant -/

theorem releaseUnlinkOn_objects_invExt (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : (st.releaseUnlinkOn c s).objects.invExt := by
  unfold releaseUnlinkOn
  split
  · dsimp only
    split
    · exact mapSchedContextInPlace_objects_invExt _ _ _ hInv
    · exact mapSchedContextInPlace_objects_invExt _ _ _ (mapSchedContextInPlace_objects_invExt _ _ _ hInv)
  · exact hInv

theorem releaseRemoveOn_objects_invExt (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : (st.releaseRemoveOn c s).objects.invExt :=
  releaseUnlinkOn_objects_invExt st c s hInv

theorem releaseLinkIn_objects_invExt (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) (hInv : st.objects.invExt) : (st.releaseLinkIn c s t).objects.invExt := by
  unfold releaseLinkIn
  dsimp only
  split
  · exact mapSchedContextInPlace_objects_invExt _ _ _ hInv
  · exact mapSchedContextInPlace_objects_invExt _ _ _ (mapSchedContextInPlace_objects_invExt _ _ _ hInv)

theorem releaseInsertOn_objects_invExt (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) (hInv : st.objects.invExt) : (st.releaseInsertOn c s t).objects.invExt := by
  unfold releaseInsertOn
  split
  · exact hInv
  · exact releaseLinkIn_objects_invExt st c s t hInv

theorem releaseRemoveAnywhere_objects_invExt (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : (st.releaseRemoveAnywhere s).objects.invExt := by
  unfold releaseRemoveAnywhere
  split
  · exact releaseRemoveOn_objects_invExt _ _ _ hInv
  · exact hInv

theorem releasePlace_objects_invExt (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : (st.releasePlace c s).objects.invExt := by
  unfold releasePlace
  split
  · split
    · exact releaseInsertOn_objects_invExt _ _ _ _ (releaseRemoveOn_objects_invExt _ _ _ hInv)
    · exact releaseRemoveOn_objects_invExt _ _ _ hInv
  · exact hInv

/-! ## The edits write the objects and the release-queue slots alone -/

/-- `sch'` is `sch` with at most its release-queue slots (the abstract queues,
the heads and the counts) rewritten. -/
def _root_.SeLe4n.Model.SchedulerState.releaseOnly (sch' sch : SchedulerState) : Prop :=
  sch' = { sch with replenishQueue := sch'.replenishQueue, releaseHeadCode := sch'.releaseHeadCode,
                    releaseCount := sch'.releaseCount }


theorem _root_.SeLe4n.Model.SchedulerState.releaseOnly.refl (sch : SchedulerState) : sch.releaseOnly sch := rfl

theorem _root_.SeLe4n.Model.SchedulerState.releaseOnly.trans {a b d : SchedulerState} (h₂ : d.releaseOnly b) (h₁ : b.releaseOnly a) :
    d.releaseOnly a := by
  unfold SchedulerState.releaseOnly at *
  calc d = { b with replenishQueue := d.replenishQueue, releaseHeadCode := d.releaseHeadCode,
                    releaseCount := d.releaseCount } := h₂
    _ = _ := by rw [h₁]

theorem _root_.SeLe4n.Model.SchedulerState.releaseOnly.setReleaseHeadOnCore {a b : SchedulerState} (h : b.releaseOnly a) (c : CoreId) (v : Nat) :
    (b.setReleaseHeadOnCore c v).releaseOnly a :=
  SchedulerState.releaseOnly.trans (b := b) rfl h

theorem _root_.SeLe4n.Model.SchedulerState.releaseOnly.setReleaseCountOnCore {a b : SchedulerState} (h : b.releaseOnly a) (c : CoreId) (v : Nat) :
    (b.setReleaseCountOnCore c v).releaseOnly a :=
  SchedulerState.releaseOnly.trans (b := b) rfl h

theorem _root_.SeLe4n.Model.SchedulerState.releaseOnly.setReplenishQueueOnCore {a b : SchedulerState} (h : b.releaseOnly a) (c : CoreId)
    (v : ReplenishQueue) : (b.setReplenishQueueOnCore c v).releaseOnly a :=
  SchedulerState.releaseOnly.trans (b := b) rfl h



/-- WS-ZA ZA6.3: `st'` is `st` with at most its objects and its release-queue
slots rewritten. -/
def releaseOnlyWrite (st' st : SystemState) : Prop :=
  st' = { st with objects := st'.objects, scheduler := st'.scheduler } ∧
    st'.scheduler.releaseOnly st.scheduler

namespace releaseOnlyWrite

theorem refl (st : SystemState) : releaseOnlyWrite st st := ⟨rfl, rfl⟩

theorem trans {a b d : SystemState} (h₂ : releaseOnlyWrite d b) (h₁ : releaseOnlyWrite b a) :
    releaseOnlyWrite d a := by
  refine ⟨?_, SchedulerState.releaseOnly.trans h₂.2 h₁.2⟩
  calc d = { b with objects := d.objects, scheduler := d.scheduler } := h₂.1
    _ = _ := by rw [h₁.1]

theorem mapSchedContextInPlace (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) : releaseOnlyWrite (st.mapSchedContextInPlace s g) st :=
  ⟨rfl, rfl⟩

theorem withScheduler {a b : SystemState} (h : releaseOnlyWrite b a) {sch : SchedulerState}
    (hs : sch.releaseOnly b.scheduler) : releaseOnlyWrite { b with scheduler := sch } a := by
  refine ⟨?_, SchedulerState.releaseOnly.trans hs h.2⟩
  show { b with scheduler := sch } = _
  conv => lhs; rw [h.1]

theorem machine {a b : SystemState} (h : releaseOnlyWrite b a) : b.machine = a.machine := by
  rw [h.1]

/-- A store's no-retype check reads the same across a release-queue edit: the
index and lifecycle are kept, and an object's kind is kept with its fields. -/
theorem storeLeavesIndexAndTypes_eq {st' st : SystemState} (h : releaseOnlyWrite st' st)
    (hA : objectsAgreeOffReleaseLinks st' st) (id : SeLe4n.ObjId) (ty : KernelObjectType) :
    storeLeavesIndexAndTypes st' id ty = storeLeavesIndexAndTypes st id ty := by
  have hI : st'.objectIndexSet = st.objectIndexSet := by rw [h.1]
  have hL : st'.lifecycle = st.lifecycle := by rw [h.1]
  have hx := hA id
  unfold storeLeavesIndexAndTypes
  rw [hI, hL]
  cases e : st.objects[id]? with
  | none =>
    cases e' : st'.objects[id]? with
    | none => rfl
    | some _ => rw [e, e'] at hx; cases hx
  | some o =>
    cases e' : st'.objects[id]? with
    | none => rw [e, e'] at hx; cases hx
    | some o' =>
      rw [e, e'] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      cases o <;> cases o' <;> simp_all [KernelObject.withoutRelease]


end releaseOnlyWrite

theorem releaseUnlinkOn_releaseOnlyWrite (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    releaseOnlyWrite (st.releaseUnlinkOn c s) st := by
  unfold releaseUnlinkOn
  split
  · dsimp only
    split
    · exact ((releaseOnlyWrite.mapSchedContextInPlace _ _ _).withScheduler
        ((SchedulerState.releaseOnly.refl _).setReleaseHeadOnCore _ _)).withScheduler
        ((SchedulerState.releaseOnly.refl _).setReleaseCountOnCore _ _)
    · exact ((releaseOnlyWrite.mapSchedContextInPlace _ _ _).trans
        (releaseOnlyWrite.mapSchedContextInPlace _ _ _)).withScheduler
        ((SchedulerState.releaseOnly.refl _).setReleaseCountOnCore _ _)
  · exact .refl _

theorem releaseRemoveOn_releaseOnlyWrite (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    releaseOnlyWrite (st.releaseRemoveOn c s) st :=
  (releaseUnlinkOn_releaseOnlyWrite st c s).withScheduler
    ((SchedulerState.releaseOnly.refl _).setReplenishQueueOnCore _ _)

theorem releaseLinkIn_releaseOnlyWrite (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) : releaseOnlyWrite (st.releaseLinkIn c s t) st := by
  unfold releaseLinkIn
  dsimp only
  split
  · exact ((releaseOnlyWrite.mapSchedContextInPlace _ _ _).withScheduler
      ((SchedulerState.releaseOnly.refl _).setReleaseHeadOnCore _ _)).withScheduler
      ((SchedulerState.releaseOnly.refl _).setReleaseCountOnCore _ _)
  · exact ((releaseOnlyWrite.mapSchedContextInPlace _ _ _).trans
      (releaseOnlyWrite.mapSchedContextInPlace _ _ _)).withScheduler
      ((SchedulerState.releaseOnly.refl _).setReleaseCountOnCore _ _)

theorem releaseInsertFresh_releaseOnlyWrite (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) : releaseOnlyWrite (st.releaseInsertFresh c s t) st :=
  (releaseLinkIn_releaseOnlyWrite st c s t).withScheduler
    ((SchedulerState.releaseOnly.refl _).setReplenishQueueOnCore _ _)

theorem releaseInsertOn_releaseOnlyWrite (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) : releaseOnlyWrite (st.releaseInsertOn c s t) st := by
  unfold releaseInsertOn
  split
  · exact .refl _
  · exact releaseInsertFresh_releaseOnlyWrite st c s t

theorem releaseRemoveAnywhere_releaseOnlyWrite (st : SystemState) (s : SeLe4n.SchedContextId) :
    releaseOnlyWrite (st.releaseRemoveAnywhere s) st := by
  unfold releaseRemoveAnywhere
  split
  · exact releaseRemoveOn_releaseOnlyWrite _ _ _
  · exact .refl _

theorem releasePlace_releaseOnlyWrite (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    releaseOnlyWrite (st.releasePlace c s) st := by
  unfold releasePlace
  split
  · split
    · exact (releaseInsertOn_releaseOnlyWrite _ _ _ _).trans (releaseRemoveOn_releaseOnlyWrite _ _ _)
    · exact releaseRemoveOn_releaseOnlyWrite _ _ _
  · exact .refl _

/-! ## Moving a context between cores -/

/-- After its removal from the queue it was on, a context is on no queue. -/
theorem releaseRemoveOn_not_queued {st : SystemState} {c : CoreId} {s : SeLe4n.SchedContextId}
    (hq : st.releaseQueuedOn c s = true) :
    (st.releaseRemoveOn c s).releaseQueuedAnywhere s = false := by
  rw [releaseQueuedAnywhere_eq_false_iff]
  intro c'
  show (st.releaseUnlinkOn c s).releaseLinkOn c' s = none
  rw [releaseLinkOn_releaseUnlinkOn st c s hq]; simp

/-- The guarded insert of a context on no queue is the fresh insert. -/
theorem releaseInsertOn_eq_fresh {st : SystemState} {c : CoreId} {s : SeLe4n.SchedContextId}
    {t : Nat} (hfree : st.releaseQueuedAnywhere s = false)
    (hsome : (st.getSchedContext? s).isSome = true) :
    st.releaseInsertOn c s t = st.releaseInsertFresh c s t := by
  unfold releaseInsertOn
  rw [if_neg]
  cases e : st.getSchedContext? s with
  | none => rw [e] at hsome; cases hsome
  | some _ => simp [hfree]

/-- A context on core `c`'s queue holds the entry its link keys. -/
theorem releaseQueueRefinedOnCore.mem_of_queued {st : SystemState} {c : CoreId}
    (h : st.releaseQueueRefinedOnCore c) {s : SeLe4n.SchedContextId}
    (hq : st.releaseQueuedOn c s = true) :
    (s, st.releaseAtOn c s) ∈ (st.scheduler.replenishQueueOnCore c).entries := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ((h.queued s).mp hq)
  rw [h.at_eq e he]; exact he

/-- A context off core `c`'s queue holds no entry there. -/
theorem releaseQueueRefinedOnCore.not_mem_of_not_queued {st : SystemState} {c : CoreId}
    (h : st.releaseQueueRefinedOnCore c) {s : SeLe4n.SchedContextId}
    (hq : st.releaseQueuedOn c s = false) (t : Nat) :
    (s, t) ∉ (st.scheduler.replenishQueueOnCore c).entries := fun m => by
  have := (h.queued s).mpr (List.mem_map.mpr ⟨_, m, rfl⟩)
  rw [hq] at this; cases this

/-- An entry naming `s` on core `c`'s queue is `s`'s keyed entry. -/
theorem releaseQueueRefinedOnCore.eq_of_mem {st : SystemState} {c : CoreId}
    (h : st.releaseQueueRefinedOnCore c) {s : SeLe4n.SchedContextId} {t : Nat}
    (m : (s, t) ∈ (st.scheduler.replenishQueueOnCore c).entries) :
    st.releaseQueuedOn c s = true ∧ st.releaseAtOn c s = t :=
  ⟨(h.queued s).mpr (List.mem_map.mpr ⟨_, m, rfl⟩), h.at_eq _ m⟩

theorem releaseInsertOn_replenishQueueOnCore_ne (st : SystemState) (c : CoreId)
    (s : SeLe4n.SchedContextId) (t : Nat) (c' : CoreId) (h : c' ≠ c) :
    (st.releaseInsertOn c s t).scheduler.replenishQueueOnCore c' =
      st.scheduler.replenishQueueOnCore c' := by
  unfold releaseInsertOn
  split
  · rfl
  · rw [releaseInsertFresh_replenishQueueOnCore, if_neg h]

/-- **A removal only ever drops entries**: every core's abstract queue after it
holds a subset of what it held before, whatever the links say. -/
theorem releaseRemoveOn_entries_subset (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (c' : CoreId) (e : SeLe4n.SchedContextId × Nat)
    (he : e ∈ ((st.releaseRemoveOn c s).scheduler.replenishQueueOnCore c').entries) :
    e ∈ (st.scheduler.replenishQueueOnCore c').entries := by
  rw [releaseRemoveOn_replenishQueueOnCore] at he
  split at he
  · rename_i hc; subst hc
    exact (List.mem_filter.mp he).1
  · exact he

/-- ...and never keeps an entry naming the removed context, on any core. -/
theorem releaseRemoveOn_entries_ne (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (e : SeLe4n.SchedContextId × Nat)
    (he : e ∈ ((st.releaseRemoveOn c s).scheduler.replenishQueueOnCore c).entries) : e.1 ≠ s := by
  rw [releaseRemoveOn_replenishQueueOnCore, if_pos rfl] at he
  intro hk
  have := (List.mem_filter.mp he).2
  simp [hk] at this

/-- On a core free for it, the removal leaves the context on no queue. -/
theorem releaseRemoveOn_not_queued_of_free {st : SystemState} {c : CoreId}
    {s : SeLe4n.SchedContextId} (hf : st.releaseFreeFor c s = true) :
    (st.releaseRemoveOn c s).releaseQueuedAnywhere s = false := by
  cases e : st.releaseCoreOf s with
  | some d =>
    have hd : d = c := (releaseFreeFor_iff st c s).mp hf d e
    subst hd
    exact releaseRemoveOn_not_queued (releaseQueuedOn_of_releaseCoreOf e)
  | none =>
    rw [releaseQueuedAnywhere_eq_false_iff]
    intro c'
    show (st.releaseUnlinkOn c s).releaseLinkOn c' s = none
    unfold releaseUnlinkOn
    rw [if_neg (by rw [releaseQueuedOn_eq, releaseLinkOn_of_releaseCoreOf_none e c]; simp)]
    exact releaseLinkOn_of_releaseCoreOf_none e c'

theorem releasePlace_agree (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    objectsAgreeOffReleaseLinks (st.releasePlace c s) st := by
  unfold releasePlace
  split
  · split
    · exact (releaseInsertOn_agree _ _ _ _).trans (releaseRemoveOn_agree _ _ _)
    · exact releaseRemoveOn_agree _ _ _
  · exact .refl _

theorem releasePlace_refined {st : SystemState} (h : st.releaseQueueRefined) (c : CoreId)
    (s : SeLe4n.SchedContextId) : (st.releasePlace c s).releaseQueueRefined := by
  unfold releasePlace
  split
  · split
    · exact releaseInsertOn_refined (releaseRemoveOn_refined h c s) _ _ _
    · exact releaseRemoveOn_refined h c s
  · exact h

/-- **The insert's refusal is dead** on a free core: after the removal the
context is on no queue and still held, so placing it always links it in. -/
theorem releasePlace_eq_fresh {st : SystemState} {c : CoreId} {s : SeLe4n.SchedContextId}
    {sc : SchedContext} {t : Nat} (hf : st.releaseFreeFor c s = true)
    (hsc : st.getSchedContext? s = some sc) (hk : sc.releaseKey? = some t) :
    st.releasePlace c s = (st.releaseRemoveOn c s).releaseInsertFresh c s t := by
  unfold releasePlace
  rw [if_pos hf, releaseKeyOf_eq_some.mpr ⟨sc, hsc, hk⟩]
  dsimp only
  refine releaseInsertOn_eq_fresh (releaseRemoveOn_not_queued_of_free hf) ?_
  rw [(releaseRemoveOn_agree st c s).getSchedContext?_isSome, hsc]; rfl

/-- **Placing writes core `c`'s abstract queue alone.** -/
theorem releasePlace_replenishQueueOnCore_ne (st : SystemState) (c : CoreId)
    (s : SeLe4n.SchedContextId) (c' : CoreId) (h : c' ≠ c) :
    (st.releasePlace c s).scheduler.replenishQueueOnCore c' =
      st.scheduler.replenishQueueOnCore c' := by
  unfold releasePlace
  split
  · split
    · rw [releaseInsertOn_replenishQueueOnCore_ne _ _ _ _ _ h,
        releaseRemoveOn_replenishQueueOnCore, if_neg h]
    · rw [releaseRemoveOn_replenishQueueOnCore, if_neg h]
  · rfl

/-- **What placing writes to core `c`'s abstract queue**: the context's entry
dropped and, when it has a place, placed there. -/
theorem releasePlace_replenishQueueOnCore_self {st : SystemState} {c : CoreId}
    {s : SeLe4n.SchedContextId} (hf : st.releaseFreeFor c s = true) :
    (st.releasePlace c s).scheduler.replenishQueueOnCore c =
      match st.releaseKeyOf s with
      | some t => ((st.scheduler.replenishQueueOnCore c).remove s).insert s t
      | none => (st.scheduler.replenishQueueOnCore c).remove s := by
  cases hk : st.releaseKeyOf s with
  | none =>
    unfold releasePlace; rw [if_pos hf, hk]; dsimp only
    rw [releaseRemoveOn_replenishQueueOnCore, if_pos rfl]
  | some t =>
    dsimp only
    obtain ⟨sc, hsc, hk'⟩ := releaseKeyOf_eq_some.mp hk
    rw [releasePlace_eq_fresh hf hsc hk', releaseInsertFresh_replenishQueueOnCore, if_pos rfl,
      releaseRemoveOn_replenishQueueOnCore, if_pos rfl]

/-- A core not free for the context is left as it was. -/
theorem releasePlace_of_not_free {st : SystemState} {c : CoreId} {s : SeLe4n.SchedContextId}
    (hf : st.releaseFreeFor c s = false) : st.releasePlace c s = st := by
  unfold releasePlace; rw [if_neg (by rw [hf]; decide)]

/-- An entry of a queue with `s` dropped and re-inserted at `t` was there
before or is `(s, t)`. -/
theorem _root_.SeLe4n.Kernel.ReplenishQueue.mem_remove_insert {q : ReplenishQueue}
    {s : SeLe4n.SchedContextId} {t : Nat} {e : SeLe4n.SchedContextId × Nat}
    (he : e ∈ ((q.remove s).insert s t).entries) : e ∈ q.entries ∨ e = (s, t) := by
  simp only [ReplenishQueue.insert, ReplenishQueue.remove] at he
  rw [insertSorted_eq_split] at he
  simp only [List.mem_append, List.mem_cons] at he
  rcases he with he | he | he
  · exact Or.inl (List.mem_filter.mp ((List.takeWhile_sublist _).subset he)).1
  · exact Or.inr he
  · exact Or.inl (List.mem_filter.mp ((List.dropWhile_sublist _).subset he)).1

theorem _root_.SeLe4n.Kernel.ReplenishQueue.mem_of_mem_remove {q : ReplenishQueue}
    {s : SeLe4n.SchedContextId} {e : SeLe4n.SchedContextId × Nat}
    (he : e ∈ (q.remove s).entries) : e ∈ q.entries :=
  (List.mem_filter.mp he).1

/-- **Placing adds no other context's entry**: every entry on any core's queue
afterwards was there before, or is the placed context's own, at its key. -/
theorem releasePlace_entries_cases (st : SystemState) (c : CoreId)
    (s : SeLe4n.SchedContextId) (c' : CoreId) (e : SeLe4n.SchedContextId × Nat)
    (he : e ∈ ((st.releasePlace c s).scheduler.replenishQueueOnCore c').entries) :
    e ∈ (st.scheduler.replenishQueueOnCore c').entries ∨
      (e.1 = s ∧ st.releaseKeyOf s = some e.2) := by
  by_cases hc : c' = c
  · subst hc
    cases hf : st.releaseFreeFor c' s with
    | false => rw [releasePlace_of_not_free hf] at he; exact Or.inl he
    | true =>
      rw [releasePlace_replenishQueueOnCore_self hf] at he
      cases hk : st.releaseKeyOf s with
      | none => rw [hk] at he; exact Or.inl (ReplenishQueue.mem_of_mem_remove he)
      | some t =>
        rw [hk] at he
        rcases ReplenishQueue.mem_remove_insert he with m | rfl
        · exact Or.inl m
        · exact Or.inr ⟨rfl, rfl⟩
  · rw [releasePlace_replenishQueueOnCore_ne st c s c' hc] at he; exact Or.inl he

theorem releasePlace_entries_provenance (st : SystemState) (c : CoreId)
    (s : SeLe4n.SchedContextId) (c' : CoreId) (e : SeLe4n.SchedContextId × Nat)
    (he : e ∈ ((st.releasePlace c s).scheduler.replenishQueueOnCore c').entries) :
    e ∈ (st.scheduler.replenishQueueOnCore c').entries ∨ e.1 = s :=
  (releasePlace_entries_cases st c s c' e he).imp id And.left

/-- **Placing keeps the queues keyed.** -/
theorem releasePlace_keyed {st : SystemState} (hK : st.releaseQueueKeyed)
    (c : CoreId) (s : SeLe4n.SchedContextId) : (st.releasePlace c s).releaseQueueKeyed := by
  refine releaseQueueKeyed_of hK (releasePlace_agree st c s) fun c' e he => ?_
  rcases releasePlace_entries_cases st c s c' e he with m | ⟨hs, hk⟩
  · exact Or.inl m
  · right; rw [(releasePlace_agree st c s).releaseKeyOf, hs]; exact hk

/-- **Placing strands no refill**: on a core free for it, a context with a place
is on that core's queue at it afterwards. -/
theorem releasePlace_mem {st : SystemState} {c : CoreId} {s : SeLe4n.SchedContextId} {t : Nat}
    (hf : st.releaseFreeFor c s = true) (hk : st.releaseKeyOf s = some t) :
    (s, t) ∈ ((st.releasePlace c s).scheduler.replenishQueueOnCore c).entries := by
  rw [releasePlace_replenishQueueOnCore_self hf, hk]
  simp only [ReplenishQueue.insert]
  rw [insertSorted_eq_split]
  simp

/-- On a core free for it, a context holding no pending refill is on no queue
after placing it. -/
theorem releasePlace_not_mem {st : SystemState} (h : st.releaseQueueRefined) {c : CoreId}
    {s : SeLe4n.SchedContextId} (hf : st.releaseFreeFor c s = true)
    (hk : st.releaseKeyOf s = none) (c' : CoreId) :
    s ∉ (st.releasePlace c s).releaseIds c' := by
  have hEq : st.releasePlace c s = st.releaseRemoveOn c s := by
    unfold releasePlace; rw [if_pos hf, hk]
  rw [hEq]
  intro m
  have hq := ((releaseRemoveOn_refined h c s c').queued s).mpr m
  have hn := (releaseQueuedAnywhere_eq_false_iff _ s).mp (releaseRemoveOn_not_queued_of_free hf) c'
  rw [releaseQueuedOn_eq, hn] at hq; cases hq

/-! ## Steps that write no release field -/

/-- A scheduler's release-queue slots: the abstract queues, the heads and the
counts. -/
def _root_.SeLe4n.Model.SchedulerState.releaseSlots (sch : SchedulerState) :
    SeLe4n.Erased (Vector SeLe4n.Kernel.ReplenishQueue SeLe4n.Kernel.Concurrency.numCores) ×
      Vector Nat SeLe4n.Kernel.Concurrency.numCores × Vector Nat SeLe4n.Kernel.Concurrency.numCores :=
  (sch.replenishQueue, sch.releaseHeadCode, sch.releaseCount)

/-- WS-ZA ZA6.3: `st'` holds `st`'s release queues exactly — every context's
link on every core, and every release-queue slot. -/
def releaseStateAgree (st' st : SystemState) : Prop :=
  ReleaseLinksAgree st' st ∧ st'.scheduler.releaseSlots = st.scheduler.releaseSlots

namespace releaseStateAgree

theorem refl (st : SystemState) : releaseStateAgree st st := ⟨.refl st, rfl⟩

theorem trans {a b d : SystemState} (h₁ : releaseStateAgree a b) (h₂ : releaseStateAgree b d) :
    releaseStateAgree a d := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- **A step holding the release queues keeps them refined.** -/
theorem refined {st st' : SystemState} (h : releaseStateAgree st' st)
    (hr : st.releaseQueueRefined) : st'.releaseQueueRefined := by
  have hS := h.2
  simp only [SchedulerState.releaseSlots, Prod.mk.injEq] at hS
  exact releaseQueueRefined_of_frame h.1 hS.1 hS.2.1 hS.2.2 hr

theorem replenishQueueOnCore {st st' : SystemState} (h : releaseStateAgree st' st) (c : CoreId) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  have hS := h.2
  simp only [SchedulerState.releaseSlots, Prod.mk.injEq] at hS
  unfold SchedulerState.replenishQueueOnCore; rw [hS.1]

theorem of_getSchedContext? {st st' : SystemState}
    (hG : ∀ s, st'.getSchedContext? s = st.getSchedContext? s)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots) : releaseStateAgree st' st :=
  ⟨.of_getSchedContext? hG, hS⟩

theorem of_objects_eq {st st' : SystemState} (hO : st'.objects = st.objects)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots) : releaseStateAgree st' st :=
  ⟨.of_objects_eq hO, hS⟩

/-- A step that keeps every context, forward and back, and writes no
release-queue slot holds the release queues. -/
theorem of_schedContexts {st st' : SystemState}
    (hF : ∀ (oid : SeLe4n.ObjId) (sc : SchedContext),
      st.objects[oid]? = some (.schedContext sc) → st'.objects[oid]? = some (.schedContext sc))
    (hB : ∀ (oid : SeLe4n.ObjId) (sc : SchedContext),
      st'.objects[oid]? = some (.schedContext sc) → st.objects[oid]? = some (.schedContext sc))
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots) : releaseStateAgree st' st := by
  refine .of_getSchedContext? (fun s => ?_) hS
  cases h1 : st.getSchedContext? s with
  | some sc =>
    exact (getSchedContext?_eq_some_iff _ _ _).mpr (hF _ sc ((getSchedContext?_eq_some_iff _ _ _).mp h1))
  | none =>
    cases h2 : st'.getSchedContext? s with
    | none => rfl
    | some sc =>
      rw [(getSchedContext?_eq_some_iff _ _ _).mpr
        (hB _ sc ((getSchedContext?_eq_some_iff _ _ _).mp h2))] at h1
      cases h1

/-- A store whose object gives its slot's release links holds the release
queues. -/
theorem storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hS : SeLe4n.Model.storeObject k o st = .ok ((), st'))
    (h : ∀ c, objReleaseLinkOn (some o) c = objReleaseLinkOn st.objects[k]? c) :
    releaseStateAgree st' st := by
  unfold SeLe4n.Model.storeObject at hS; cases hS; exact ⟨.insert hInv rfl h, rfl⟩

/-- A store of a thread over a thread holds the release queues. -/
theorem storeObject_tcb {st st' : SystemState} {k : SeLe4n.ObjId} {t old : TCB}
    (hInv : st.objects.invExt) (hS : SeLe4n.Model.storeObject k (.tcb t) st = .ok ((), st'))
    (hOld : st.objects[k]? = some (.tcb old)) : releaseStateAgree st' st :=
  storeObject hInv hS fun _ => by rw [hOld]; rfl

/-- A context update keeping its link fields holds the release queues. -/
theorem updateSchedContext (st : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hInv : st.objects.invExt)
    (hf : ∀ sc, (f sc).releaseNextCode = sc.releaseNextCode ∧
      (f sc).releaseCoreCode = sc.releaseCoreCode ∧ (f sc).releaseAt = sc.releaseAt) :
    releaseStateAgree (st.updateSchedContext scId f) st := by
  refine ⟨fun c s => ?_, by rw [updateSchedContext_scheduler]⟩
  unfold releaseLinkOn
  by_cases hs : s = scId
  · subst hs
    rw [updateSchedContext_getSchedContext?_self _ _ _ hInv]
    cases st.getSchedContext? s with
    | none => rfl
    | some sc =>
      simp only [Option.map_some]
      obtain ⟨h1, h2, h3⟩ := hf sc
      unfold SchedContext.releaseLinkOn
      rw [h1, h2, h3]
  · rw [updateSchedContext_getSchedContext?_ne _ _ _ hInv _
      (fun h => hs (SeLe4n.SchedContextId.toObjId_injective _ _ h).symm)]

end releaseStateAgree
