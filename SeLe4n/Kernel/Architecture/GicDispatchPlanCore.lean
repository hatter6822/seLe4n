-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude

/-!
# WS-RC R6.A.1a (DEEP-ARCH-03) — GIC dispatch plan core (upstream)

This module hosts the **upstream-only** pieces of the GIC dispatch
bridge: the `InterruptOp` algebra, the symbolic `interruptDispatchPlan`,
the five plan-ordering witnesses, and the static
`gicDispatchPlanStaticInvariant`.

## Why a separate upstream file

The import DAG is:

```
Kernel.API  →  Architecture.Invariant     (Kernel.API imports it)
Architecture.ExceptionModel  →  Kernel.API
Architecture.InterruptDispatch  →  Kernel.API
```

So both `Architecture.ExceptionModel` and `Architecture.InterruptDispatch`
are strictly **downstream** of `Architecture.Invariant`.  If
`Architecture.Invariant` is to add the static GIC plan invariant
(`gicDispatchPlanStaticInvariant`) as a conjunct of
`proofLayerInvariantBundle` — required by the audit plan
(`AUDIT_v0.30.11_WORKSTREAM_PLAN.md` §10.6 R6.A.3) — then the
definitions backing that invariant must live in a file **upstream** of
`Architecture.Invariant`.

This module:

1. Imports only `SeLe4n.Prelude` (no `Kernel.API` chain), so it sits
   far upstream of `Architecture.Invariant`.
2. Defines `InterruptId` (replacing the one previously in
   `Architecture.InterruptDispatch.lean`; that file now imports this
   one and re-exports the type).
3. Defines `InterruptOp` and `interruptDispatchPlan` with the AN8-C
   ordering `[.ack id, .eoi id, .handle id]` (H-19 hardening: handler
   runs on post-EOI state so a faulting handler cannot leave the
   INTID active on the GIC — see `Architecture.InterruptDispatch`
   `interruptDispatchSequence` for the executable semantics).
4. Defines the static invariant `gicDispatchPlanStaticInvariant`
   (the **closed**-Prop universal property of the plan ordering, with
   no `SystemState` dependence) and discharges it unconditionally via
   `gicDispatchPlanStaticInvariant_holds`.

The **runtime-delegation** half of the bridge (showing that
`dispatchException .irq ≡ interruptDispatchSequence`) lives in
`Architecture.ExceptionModel` because it references
`dispatchException` and the executable `interruptDispatchSequence`,
both of which require the full `Kernel.API` chain.
-/

namespace SeLe4n.Kernel.Architecture

/-- WS-RC R6.A.1a (DEEP-ARCH-03): GIC-400 interrupt ID for RPi5
    (BCM2712).  Bounded to 224 INTIDs (0–223): SGIs (0–15), PPIs
    (16–31), SPIs (32–223).

    Moved here from `Architecture.InterruptDispatch.lean` at WS-RC R6
    deferred-completion so it is upstream of `Architecture.Invariant`
    and can be referenced by the static GIC plan invariant conjunct
    of `proofLayerInvariantBundle`.

    Historical comment from `InterruptDispatch.lean`: "This bound is
    RPi5/BCM2712-specific. The GIC-400 architecture supports up to
    480 INTIDs, but BCM2712 only implements 192 SPIs (32–223). A
    future multi-platform build would parameterize this bound." -/
abbrev InterruptId := Fin 224

/-- WS-RC R6.A.1a (DEEP-ARCH-03): Symbolic algebra of GIC-400
    operations performed during interrupt dispatch.  Each constructor
    captures one hardware-level step and carries the affected
    `InterruptId` so dispatch plans for distinct INTIDs are
    distinguishable at the type level. -/
inductive InterruptOp where
  /-- Read GICC_IAR to acknowledge the interrupt. -/
  | ack    (id : InterruptId)
  /-- Write GICC_EOIR to retire the interrupt. -/
  | eoi    (id : InterruptId)
  /-- Run the registered handler for the interrupt. -/
  | handle (id : InterruptId)
  deriving Repr, DecidableEq

/-- WS-RC R6.A.1a (DEEP-ARCH-03): The canonical GIC dispatch plan for
    any handled INTID.

    AN8-C (H-19) ordering: `acknowledge → EOI → handle`.  The handler
    runs on the post-EOI state so a panicking or long-running handler
    cannot leave the INTID active on the GIC.  See
    `interruptDispatchSequence`
    (`Architecture/InterruptDispatch.lean`) and `dispatch_irq` in
    `rust/sele4n-hal/src/gic.rs`.

    For spurious INTIDs (≥ 1020 per GIC-400 spec) and out-of-range
    INTIDs (∈ [224, 1020)) the plan is **not** applicable — the
    dispatch returns the input state unchanged at the Lean layer (the
    HAL emits a raw-IAR EOI for out-of-range cases to prevent GIC
    lockup).  The plan applies only when
    `acknowledgeInterrupt id.val = .ok id`, i.e. the dispatch actually
    enters the handled branch. -/
def interruptDispatchPlan (id : InterruptId) : List InterruptOp :=
  [.ack id, .eoi id, .handle id]

/-- WS-RC R6.A.1a: The dispatch plan always contains exactly three
    operations.  Used by downstream consumers that fold over the plan
    and need a length bound up front. -/
theorem interruptDispatchPlan_length (id : InterruptId) :
    (interruptDispatchPlan id).length = 3 := rfl

/-- WS-RC R6.A.1a: AN8-C ordering, first slot — the acknowledge
    operation is always the head of the plan.  Captures the invariant
    that GIC dispatch always begins by reading GICC_IAR. -/
theorem interruptDispatchPlan_ack_head (id : InterruptId) :
    (interruptDispatchPlan id).head? = some (.ack id) := rfl

/-- WS-RC R6.A.1a: AN8-C ordering, second slot — the end-of-interrupt
    operation always immediately follows the acknowledge.  Captures
    the H-19 hardening that retires the INTID on the GIC *before* the
    handler body runs, so a faulting or long-running handler cannot
    leave the INTID active. -/
theorem interruptDispatchPlan_eoi_second (id : InterruptId) :
    (interruptDispatchPlan id)[1]? = some (.eoi id) := rfl

/-- WS-RC R6.A.1a: AN8-C ordering, third slot — the handler operation
    runs last in the plan, after the INTID has been retired on the
    GIC.  Mirrors the runtime behaviour of `interruptDispatchSequence`
    after the AN8-C reordering. -/
theorem interruptDispatchPlan_handle_third (id : InterruptId) :
    (interruptDispatchPlan id)[2]? = some (.handle id) := rfl

/-- WS-RC R6.A.1a: AN8-C ordering, decomposed structurally — the plan
    splits as `[.ack id] ++ [.eoi id] ++ [.handle id]`.  This is the
    cite-friendly decomposition matching the plan's pseudocode
    (`ack id ++ eoi id ++ handle id`). -/
theorem interruptDispatchPlan_decomposes (id : InterruptId) :
    interruptDispatchPlan id = [.ack id] ++ [.eoi id] ++ [.handle id] := rfl

/-- WS-RC R6.A.3 (DEEP-ARCH-03): Static GIC dispatch plan
    invariant.  This is the **closed**-Prop universal property of
    `interruptDispatchPlan`: every `InterruptId` yields the
    canonical AN8-C-ordered three-element list `[.ack, .eoi, .handle]`.

    The invariant has no `SystemState` dependence — it is a static
    structural property of the dispatch-plan function.  This makes it
    suitable to add as a conjunct of `proofLayerInvariantBundle` in
    `Architecture/Invariant.lean`: every state trivially satisfies
    it, so preservation through any kernel transition is by the
    single witness `gicDispatchPlanStaticInvariant_holds`.

    The **runtime-delegation** half of the GIC bridge (showing that
    `dispatchException .irq` semantics delegate to
    `interruptDispatchSequence` over `SystemState`) is a stronger
    property and lives in `Architecture.ExceptionModel` as
    `GICDispatchBridge` / `gicDispatchPlanInvariant` / the bridge
    theorem `exception_irq_dispatches_via_interrupt_dispatch`.
    Consumers wanting the full bridge use
    `Architecture.ArchitectureInvariantBundle`. -/
def gicDispatchPlanStaticInvariant : Prop :=
  ∀ id : InterruptId,
    interruptDispatchPlan id = [.ack id, .eoi id, .handle id]

/-- WS-RC R6.A.3 (DEEP-ARCH-03): The static GIC plan invariant always
    holds — it is a pure type-level property of the
    `interruptDispatchPlan` function and decides by `rfl` at each
    `InterruptId`. -/
theorem gicDispatchPlanStaticInvariant_holds :
    gicDispatchPlanStaticInvariant :=
  fun _ => rfl

end SeLe4n.Kernel.Architecture
