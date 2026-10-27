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
A released ASID's TLB shootdown round (`asidReleaseRound`): one local
`TLBI ASIDE1` and one coalescing `.aside1` round to the remote cores, which the
final-delete retire posts for an address-space root it erases, with its framing
lemmas; and the carve's clean-to-PoU discharge for a zeroed frame.

WS-ZA ZA5.4 part 14 retired the in-place retype this module was written for
(`lifecycleRetypeWithCleanup`, `lifecycleRetypeDirectWithCleanup` and their
shootdown, per-core and instruction-cache wrappers): every object is now carved
from an untyped.  What remains is what the retire and the carve consume.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- A released ASID's shootdown round
-- ============================================================================

/-- **WS-SM SM7.F.4(b)(iii)** (one released ASID's round): one
`tlbFlushByASIDWithShootdown` — local scalar `TLBI ASIDE1` then the coalescing
`.aside1` round to the remote targets.  The final-delete retire posts it for an
address-space root it erases (`retireRecordedObject`), so every PE leaves the
root before the next carve can hand its page out. -/
def asidReleaseRound (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (a : SeLe4n.ASID) (s : SystemState) : SystemState :=
  Architecture.tlbShootdownBroadcastCoalescing
    { s with tlb := adapterFlushTlbByAsid s.tlb a }
    executingCore (Architecture.shootdownTargets executingCore)
    (Architecture.encodeAsidInvalidation a)

-- ----------------------------------------------------------------------------
-- WS-SM SM7.F.4(b)(iii): what the round writes
-- ----------------------------------------------------------------------------

/-- **WS-SM SM7.F.4(b)(iii)**: the round frames the object store. -/
theorem asidReleaseRound_objects
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (a : SeLe4n.ASID) (s : SystemState) :
    (asidReleaseRound executingCore a s).objects = s.objects := by
  unfold asidReleaseRound
  rw [(Architecture.tlbShootdownBroadcastCoalescing_frame _ _ _ _).1]

/-- **WS-SM SM8.B.2**: the round frames the scheduler.

TLB maintenance is not scheduling: the step writes the scalar `tlb` and posts to
`tlbShootdown`, and neither is a per-core observable slot. -/
theorem asidReleaseRound_scheduler
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (a : SeLe4n.ASID) (s : SystemState) :
    (asidReleaseRound executingCore a s).scheduler = s.scheduler := by
  unfold asidReleaseRound
  rw [(Architecture.tlbShootdownBroadcastCoalescing_frame _ _ _ _).2.1]

/-- **WS-SM SM8.B.2**: the round frames the machine, register banks
included. -/
theorem asidReleaseRound_machine
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (a : SeLe4n.ASID) (s : SystemState) :
    (asidReleaseRound executingCore a s).machine = s.machine := by
  unfold asidReleaseRound
  rw [(Architecture.tlbShootdownBroadcastCoalescing_frame _ _ _ _).2.2.1]

/-- **WS-SM SM7.F.4(b)(iii)**: the round frames the ASID table. -/
theorem asidReleaseRound_asidTable
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (a : SeLe4n.ASID) (s : SystemState) :
    (asidReleaseRound executingCore a s).asidTable = s.asidTable := rfl

/-- **WS-SM SM7.F.4(b)(iii)**: the round's shootdown effect is the coalescing
round posting. -/
theorem asidReleaseRound_tlbShootdown
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (a : SeLe4n.ASID) (s : SystemState) :
    (asidReleaseRound executingCore a s).tlbShootdown =
      Architecture.postShootdownRoundCoalescing s.tlbShootdown executingCore
        (Architecture.shootdownTargets executingCore)
        (Architecture.encodeAsidInvalidation a) := rfl

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
