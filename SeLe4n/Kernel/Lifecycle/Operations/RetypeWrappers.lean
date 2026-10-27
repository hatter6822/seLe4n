-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.ScrubAndUntyped
import SeLe4n.Model.Object.Unshare
import SeLe4n.Kernel.Architecture.TlbShootdownProtocol
import SeLe4n.Kernel.Architecture.PerCoreTlbModel
import SeLe4n.Kernel.Architecture.PerCoreCacheModel

/-!
The per-ASID TLB shootdown round fold the untyped reset posts
(`untypedResetWithShootdown`): one local `TLBI ASIDE1` and one coalescing
`.aside1` round to the remote cores per ASID the reset retires, with its pure
framing lemmas; and the carve's clean-to-PoU discharge for a zeroed frame.

WS-ZA ZA5.4 part 14 retired the in-place retype this module was written for
(`lifecycleRetypeWithCleanup`, `lifecycleRetypeDirectWithCleanup` and their
shootdown, per-core and instruction-cache wrappers): every object is now carved
from an untyped.  What remains is what the reset and the carve consume.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- The per-ASID shootdown round fold
-- ============================================================================

/-- **WS-SM SM7.F.4(b)(iii)** (the pure per-ASID step of the round fold):
one `tlbFlushByASIDWithShootdown` — local scalar `TLBI ASIDE1` then the coalescing
`.aside1` round to the remote targets. -/
def retypeAsidRoundStep (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (a : SeLe4n.ASID) (s : SystemState) : SystemState :=
  Architecture.tlbShootdownBroadcastCoalescing
    { s with tlb := adapterFlushTlbByAsid s.tlb a }
    executingCore (Architecture.shootdownTargets executingCore)
    (Architecture.encodeAsidInvalidation a)

/-- **WS-SM SM7.F.4(b)(iii)** (the pure state the round fold commits): the
left-fold of `retypeAsidRoundStep` over the flush set. -/
def retypeAsidRoundFold (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (asids : List SeLe4n.ASID) (s : SystemState) : SystemState :=
  asids.foldl (fun st a => retypeAsidRoundStep executingCore a st) s

/-- **WS-SM SM7.F.4(b)(iii)** (the shootdown-state projection of the round fold):
the fold of coalescing round postings, one per flushed ASID. -/
def roundFoldSd (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (asids : List SeLe4n.ASID)
    (sd : Architecture.TlbShootdownState) :
    Architecture.TlbShootdownState :=
  asids.foldl (fun s a => Architecture.postShootdownRoundCoalescing s executingCore
    (Architecture.shootdownTargets executingCore)
    (Architecture.encodeAsidInvalidation a)) sd

-- ----------------------------------------------------------------------------
-- WS-SM SM7.F.4(b)(iii): pure closed forms + framing for the round fold
-- ----------------------------------------------------------------------------

/-- **WS-SM SM7.F.4(b)(iii)**: the round step frames the object store. -/
theorem retypeAsidRoundStep_objects
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (a : SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundStep executingCore a s).objects = s.objects := by
  unfold retypeAsidRoundStep
  rw [(Architecture.tlbShootdownBroadcastCoalescing_frame _ _ _ _).1]

/-- **WS-SM SM8.B.2**: the round step frames the scheduler.

TLB maintenance is not scheduling: the step writes the scalar `tlb` and posts to
`tlbShootdown`, and neither is a per-core observable slot. -/
theorem retypeAsidRoundStep_scheduler
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (a : SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundStep executingCore a s).scheduler = s.scheduler := by
  unfold retypeAsidRoundStep
  rw [(Architecture.tlbShootdownBroadcastCoalescing_frame _ _ _ _).2.1]

/-- **WS-SM SM8.B.2**: the round step frames the machine, register banks
included. -/
theorem retypeAsidRoundStep_machine
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (a : SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundStep executingCore a s).machine = s.machine := by
  unfold retypeAsidRoundStep
  rw [(Architecture.tlbShootdownBroadcastCoalescing_frame _ _ _ _).2.2.1]

/-- **WS-SM SM7.F.4(b)(iii)**: the round step frames the ASID table. -/
theorem retypeAsidRoundStep_asidTable
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (a : SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundStep executingCore a s).asidTable = s.asidTable := rfl

/-- **WS-SM SM7.F.4(b)(iii)**: the round step's shootdown effect is the coalescing
round posting. -/
theorem retypeAsidRoundStep_tlbShootdown
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (a : SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundStep executingCore a s).tlbShootdown =
      Architecture.postShootdownRoundCoalescing s.tlbShootdown executingCore
        (Architecture.shootdownTargets executingCore)
        (Architecture.encodeAsidInvalidation a) := rfl

/-- The round fold writes no reference table: each round writes shootdown
state alone. -/
theorem retypeAsidRoundFold_referenceTables
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (asids : List SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundFold executingCore asids s).referenceTables = s.referenceTables := by
  induction asids generalizing s with
  | nil => rfl
  | cons a rest ih =>
      have h1 : retypeAsidRoundFold executingCore (a :: rest) s
        = retypeAsidRoundFold executingCore rest (retypeAsidRoundStep executingCore a s) := rfl
      rw [h1, ih]; rfl

/-- **WS-SM SM7.F.4(b)(iii)**: the round fold frames the object store. -/
theorem retypeAsidRoundFold_objects
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (asids : List SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundFold executingCore asids s).objects = s.objects := by
  induction asids generalizing s with
  | nil => rfl
  | cons a rest ih =>
      have h1 : retypeAsidRoundFold executingCore (a :: rest) s
        = retypeAsidRoundFold executingCore rest (retypeAsidRoundStep executingCore a s) := rfl
      rw [h1, ih, retypeAsidRoundStep_objects]

/-- **WS-SM SM8.B.2**: the round fold frames the scheduler — one round per
flushed ASID, none of them scheduling. -/
theorem retypeAsidRoundFold_scheduler
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (asids : List SeLe4n.ASID)
    (s : SystemState) :
    (retypeAsidRoundFold executingCore asids s).scheduler = s.scheduler := by
  induction asids generalizing s with
  | nil => rfl
  | cons a rest ih =>
      have h1 : retypeAsidRoundFold executingCore (a :: rest) s
        = retypeAsidRoundFold executingCore rest (retypeAsidRoundStep executingCore a s) := rfl
      rw [h1, ih, retypeAsidRoundStep_scheduler]

/-- **WS-SM SM8.B.2**: the round fold frames the machine. -/
theorem retypeAsidRoundFold_machine
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (asids : List SeLe4n.ASID)
    (s : SystemState) :
    (retypeAsidRoundFold executingCore asids s).machine = s.machine := by
  induction asids generalizing s with
  | nil => rfl
  | cons a rest ih =>
      have h1 : retypeAsidRoundFold executingCore (a :: rest) s
        = retypeAsidRoundFold executingCore rest (retypeAsidRoundStep executingCore a s) := rfl
      rw [h1, ih, retypeAsidRoundStep_machine]

/-- **WS-SM SM7.F.4(b)(iii)**: the round fold frames the ASID table. -/
theorem retypeAsidRoundFold_asidTable
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (asids : List SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundFold executingCore asids s).asidTable = s.asidTable := by
  induction asids generalizing s with
  | nil => rfl
  | cons a rest ih =>
      have h1 : retypeAsidRoundFold executingCore (a :: rest) s
        = retypeAsidRoundFold executingCore rest (retypeAsidRoundStep executingCore a s) := rfl
      rw [h1, ih, retypeAsidRoundStep_asidTable]

/-- **WS-SM SM7.F.4(b)(iii)**: the round fold's shootdown effect is the coalescing
round-posting fold. -/
theorem retypeAsidRoundFold_tlbShootdown
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (asids : List SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundFold executingCore asids s).tlbShootdown =
      roundFoldSd executingCore asids s.tlbShootdown := by
  induction asids generalizing s with
  | nil => rfl
  | cons a rest ih =>
      have h1 : retypeAsidRoundFold executingCore (a :: rest) s
        = retypeAsidRoundFold executingCore rest (retypeAsidRoundStep executingCore a s) := rfl
      have h2 : roundFoldSd executingCore (a :: rest) s.tlbShootdown
        = roundFoldSd executingCore rest
            (Architecture.postShootdownRoundCoalescing s.tlbShootdown executingCore
              (Architecture.shootdownTargets executingCore)
              (Architecture.encodeAsidInvalidation a)) := rfl
      rw [h1, ih, retypeAsidRoundStep_tlbShootdown, h2]

/-- **WS-BP post-landing audit (`v0.36.32`)** (the carve's obligation
discharged): the scrub of a RAM frame records one write, and that write's own
maintenance discharges the `.carveScrub` clean-to-PoU obligation over exactly
the page the scrub zeroes.

The clean rides **on** the scrub's physical write — the HAL performs
`PhysicalWrite.icacheMaintenance` as the last step of `apply_physical_write` —
because the zero is itself a deferred write the seam performs, and a clean
recorded as a separate ledger entry could be emitted in some order other than
right after the zero it cleans.  It would
be **false** at the pre-`v0.36.32` model, where the zeroing owed nothing and a
thread could map a freshly carved frame executable with its zeroes still in the
data cache and its previous owner's bytes at the Point of Unification. -/
theorem carveZeroFrame_discharges_carveScrub_obligation (st : SystemState)
    (frame : FrameObject) (hRam : frame.isDevice = false) :
    ∃ w op, (carveZeroFrame st frame).pendingPhysicalWrites =
        st.pendingPhysicalWrites ++ [w] ∧
      w.icacheMaintenance = some op ∧
      Architecture.dischargesPoUClean op frame.base SeLe4n.pageBytes = true := by
  obtain ⟨op, hOp, hDis⟩ := Architecture.zeroPage_discharges_obligation frame.base
  exact ⟨.zeroPage frame.base, op, carveZeroFrame_pendingPhysicalWrites st frame hRam,
    hOp, hDis⟩

end SeLe4n.Kernel
