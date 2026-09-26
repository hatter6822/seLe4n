-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.Architecture.PageTeardown

/-!
# Frame finalisation — destroying a frame capability unmaps what it mapped

**WS-BP BP7.1 (`v0.36.7`).**  A `VSpaceRoot` records a physical address, not
the capability that installed it, so until this version destroying a frame
capability — by `.cspaceDelete`, or as a descendant swept by `.cspaceRevoke` —
left its mapping in place, and the thread whose address space held it kept
reading and writing a page it no longer held any authority over, until some
holder of the untyped capability reset the untyped.  In seL4 a frame capability
records its mapping (`capFMappedASID`, `capFMappedAddress`) and destroying it
finalises it (`finaliseCap` → `unmapPage`); revoking authority over memory
therefore revokes access to it.

This module is that finalisation.  `.vspaceMap` records the mapping on the
invoked frame capability (`Capability.mapping`, written by
`cspaceRecordFrameMapping`); a derivation — a copy, a mint, an IPC transfer —
does not carry it; and the two destroying arms are composites here:

* `cspaceDeleteSlotFinalising` — the delete, then the page the destroyed
  capability's record names (`slotMappedPages`, read from the slot the delete
  destroys) removed;
* `cspaceRevokeCdtFinalising` — the revocation, which reports the pages of
  exactly the capabilities it destroyed (`cspaceRevokeCdt`'s result,
  `revokeCdtFoldBody_records`), then those pages removed.

Both remove pages through `unmapLivePages`, the untyped reset's own teardown, so
a page is removed only while its address space still maps the address to that
frame: a record gone stale removes nothing that is not its own.  Both then
**decide** that no destroyed capability's page survives (`livePagesCleared`) and
refuse otherwise — the check cannot fail on a well-formed state, and the payoff
theorems (`cspaceDeleteSlotFinalising_ok_unmapped`,
`cspaceRevokeCdtFinalising_ok_unmapped`) are read off it.

The one other way a capability can be destroyed is the destruction of the CNode
holding it; the retype of a CNode refuses while any slot holds a capability that
records a mapping (`CNode.holdsFrameMappingRecord`, `.revocationRequired`):
delete those capabilities first, which unmaps.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  Is a capability's mapping still live?
-- ============================================================================

/-- **The capability's recorded mapping is still in place**: it records a
mapping, targets a frame, and the address space still maps the recorded address
to that frame.  What `.vspaceMap` refuses to overwrite — a capability maps its
frame once, as in seL4, and mapping it again takes a copy. -/
def capabilityMappingLive (st : SystemState) (cap : Capability) : Bool :=
  match capabilityMappedPage st cap with
  | some p => mappedPageLive st p
  | none => false

-- ============================================================================
-- §2  The teardown, checked
-- ============================================================================

/-- **Remove the destroyed capabilities' pages, then decide none survives.** -/
def finaliseFramePages (executingCore : Concurrency.CoreId) (pages : List MappedPage) :
    Kernel Unit :=
  fun st =>
    match unmapLivePages executingCore pages st with
    | .error e => .error e
    | .ok ((), st1) =>
      if !livePagesCleared st1 pages then .error .illegalState
      else .ok ((), st1)

/-- What a successful teardown is: the unmap pass, and the decided result. -/
theorem finaliseFramePages_ok (ec : Concurrency.CoreId) (pages : List MappedPage)
    (st st' : SystemState) (h : finaliseFramePages ec pages st = .ok ((), st')) :
    unmapLivePages ec pages st = .ok ((), st') ∧ livePagesCleared st' pages = true := by
  unfold finaliseFramePages at h
  cases hU : unmapLivePages ec pages st with
  | error e => rw [hU] at h; cases h
  | ok pr =>
    obtain ⟨u, st1⟩ := pr; cases u
    rw [hU] at h
    simp only at h
    cases hC : livePagesCleared st1 pages
    · rw [hC] at h; cases h
    · rw [hC] at h
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq,
        Prod.mk.injEq, true_and] at h
      subst h
      exact ⟨rfl, hC⟩

/-- **The teardown is a VSpace-root-only write** that keeps the scheduler and the
object table's invariant. -/
theorem finaliseFramePages_ok_frame (ec : Concurrency.CoreId) (pages : List MappedPage)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (h : finaliseFramePages ec pages st = .ok ((), st')) :
    st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler :=
  unmapLivePages_ok_frame ec pages st st' hObjInv (finaliseFramePages_ok ec pages st st' h).1

-- ============================================================================
-- §3  The finalising delete
-- ============================================================================

/-- **`.cspaceDelete`: delete the capability in `addr`, then remove the mapping it
records.**  The page is read off the slot the delete destroys, on the state the
delete runs on; the delete writes only CNodes and the CDT, so the page is still
the one the destroyed capability named when the teardown runs. -/
def cspaceDeleteSlotFinalising (executingCore : Concurrency.CoreId) (addr : CSpaceAddr) :
    Kernel Unit :=
  fun st =>
    match cspaceDeleteSlot addr st with
    | .error e => .error e
    | .ok ((), st1) => finaliseFramePages executingCore (slotMappedPages st addr) st1

/-- What a successful finalising delete is: the delete, then the teardown of the
page the destroyed capability recorded. -/
theorem cspaceDeleteSlotFinalising_ok (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    ∃ st1, cspaceDeleteSlot addr st = .ok ((), st1) ∧
      finaliseFramePages ec (slotMappedPages st addr) st1 = .ok ((), st') := by
  unfold cspaceDeleteSlotFinalising at h
  cases hD : cspaceDeleteSlot addr st with
  | error e => rw [hD] at h; cases h
  | ok pr => obtain ⟨u, st1⟩ := pr; cases u; rw [hD] at h; exact ⟨st1, rfl, h⟩

/-- **The payoff: no mapping the deleted capability recorded survives it.**  If
the capability in `addr` recorded a mapping of a frame, that frame's page is not
mapped at the recorded address in the post-state. -/
theorem cspaceDeleteSlotFinalising_ok_unmapped (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st'))
    (cap : Capability) (hCap : SystemState.lookupSlotCap st addr = some cap)
    (p : MappedPage) (hP : capabilityMappedPage st cap = some p) :
    mappedPageLive st' p = false := by
  obtain ⟨_, -, hF⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' h
  refine livePagesCleared_spec (finaliseFramePages_ok ec _ _ st' hF).2 p ?_
  simp [slotMappedPages, hCap, hP]

-- ============================================================================
-- §4  The finalising revocation
-- ============================================================================

/-- **`.cspaceRevoke`: revoke the capability in `addr`, then remove every mapping
a destroyed capability recorded.**  `cspaceRevokeCdt` reports the pages of
exactly the capabilities its traversal destroyed (`revokeCdtFoldBody_records`). -/
def cspaceRevokeCdtFinalising (executingCore : Concurrency.CoreId) (addr : CSpaceAddr) :
    Kernel Unit :=
  fun st =>
    match cspaceRevokeCdt addr st with
    | .error e => .error e
    | .ok (pages, st1) => finaliseFramePages executingCore pages st1

/-- What a successful finalising revocation is: the revocation, and the
teardown of the pages its destroyed capabilities recorded. -/
theorem cspaceRevokeCdtFinalising_ok (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    ∃ pages st1, cspaceRevokeCdt addr st = .ok (pages, st1) ∧
      finaliseFramePages ec pages st1 = .ok ((), st') := by
  unfold cspaceRevokeCdtFinalising at h
  cases hR : cspaceRevokeCdt addr st with
  | error e => rw [hR] at h; cases h
  | ok pr =>
    obtain ⟨pages, st1⟩ := pr
    rw [hR] at h
    exact ⟨pages, st1, rfl, h⟩

/-- **The payoff: no reported page survives the revocation.**  With
`revokeCdtFoldBody_records` — each step reports the page of the
capability it destroys — this is the statement that a revoked frame capability's
mapping is gone. -/
theorem cspaceRevokeCdtFinalising_ok_unmapped (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    ∃ pages, (∃ st1, cspaceRevokeCdt addr st = .ok (pages, st1)) ∧
      ∀ p ∈ pages, mappedPageLive st' p = false := by
  obtain ⟨pages, st1, hC, hF⟩ := cspaceRevokeCdtFinalising_ok ec addr st st' h
  exact ⟨pages, ⟨st1, hC⟩, livePagesCleared_spec (finaliseFramePages_ok ec _ _ _ hF).2⟩

end SeLe4n.Kernel
