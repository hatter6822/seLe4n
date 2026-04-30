-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.Contract
import SeLe4n.Platform.Sim.RuntimeContract
import SeLe4n.Platform.Sim.BootContract
import SeLe4n.Platform.Sim.ProofHooks
-- WS-RC R3 (DEEP-BOOT-01): the simulation's minimal boot VSpaceRoot
-- (a single read-only identity mapping) and its boot-safety predicate
-- live inside this module.  The reusable W^X / asid / paddr predicates
-- are imported from RPi5.VSpaceBoot — they are platform-neutral
-- well-formedness shapes despite being defined alongside the RPi5
-- canonical root.
import SeLe4n.Platform.RPi5.VSpaceBoot
import SeLe4n.Kernel.Architecture.VSpace
import SeLe4n.Kernel.Architecture.AsidManager
import SeLe4n.Model.Object.Structures

/-!
# Simulation Platform Binding

> **STATUS: production binding** (typeclass instance reachable from
> `SeLe4n.lean`).  The simulation `PlatformBinding` instance composed
> here is in the production import chain; the substantive simulation
> path is exercised by `SeLe4n.Testing.MainTraceHarness` and the test
> tier suites.  See `docs/spec/SELE4N_SPEC.md` §8.15 for the activation
> roadmap.

Composed `PlatformBinding` instance for the simulation target. This is the
platform used by trace harnesses, negative-state suites, and development
testing. It bundles permissive runtime contracts with trivially-true boot
and interrupt contracts.

## Machine configuration

The simulation platform declares an idealized 64-bit machine with:
- 64-bit registers and 48-bit virtual / 52-bit physical addressing
- 4 KiB pages
- 16-bit ASID space (65536 entries)
- A single 256 MiB RAM region starting at physical address 0

These values match common ARM64 defaults and enable the trace harness to
exercise scheduler, IPC, and VSpace paths without hitting artificial bounds.
-/

namespace SeLe4n.Platform.Sim

open SeLe4n
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.RobinHood
open SeLe4n.Model

-- ============================================================================
-- WS-RC R3 (DEEP-BOOT-01) — Simulation boot VSpaceRoot
-- ============================================================================

/-- **WS-RC R3 (DEEP-BOOT-01)**: Reserved ObjId for the simulation
    boot VSpaceRoot.  Same numeric value as `rpi5BootVSpaceRootObjId`
    by convention — the boot VSpace ObjId is platform-reserved on
    every platform binding.  `ObjId.ofNat 1` is the smallest
    non-sentinel ObjId (`ObjId.sentinel = ⟨0⟩` per Prelude.lean
    H-06/WS-E3 is reserved as "unallocated").  The
    `bootVSpaceRootObjIdDistinct` runtime gate in `Platform.Boot`
    rejects configs whose `initialObjects` collide with this ObjId. -/
def simBootVSpaceRootObjId : SeLe4n.ObjId := SeLe4n.ObjId.ofNat 1

/-- **WS-RC R3**: Minimal page-permissions used by the simulation boot
    VSpaceRoot — a read-only, non-executable, kernel-only entry.
    Non-cacheable to keep the simulation hardware-agnostic. -/
private def simBootPerms : PagePermissions :=
  { read := true, write := false, execute := false, user := false, cacheable := false }

/-- **WS-RC R3**: Simulation boot VSpaceRoot — a minimal VSpaceRoot at
    ASID 0 with a single read-only identity mapping at virtual /
    physical address `0x1000`.  Satisfies the five
    `bootSafeVSpaceRoot` conjuncts (asid bounded, W^X compliant,
    non-empty mappings, paddr < 2^44, vaddr canonical < 2^48) but
    does not exercise any hardware-specific MMIO regions because the
    simulation harness runs entirely in software.

    Structurally parallel to RPi5's `rpi5BootVSpaceRoot` so the
    simulation `PlatformBinding` instance can also exercise the
    `installBootVSpaceRoot` path during gated boot, providing
    end-to-end parity for the trace harness without depending on
    BCM2712 device addresses. -/
def simBootVSpaceRoot : VSpaceRoot :=
  { asid := ASID.ofNat 0
    mappings := (RHTable.empty 16 : RHTable VAddr (PAddr × PagePermissions)).insert
      (VAddr.ofNat 0x1000) (PAddr.ofNat 0x1000, simBootPerms) }

/-- **WS-RC R3**: The simulation boot VSpaceRoot is in ASID 0. -/
theorem simBootVSpaceRoot_asid : simBootVSpaceRoot.asid = ASID.ofNat 0 := rfl

/-- **WS-RC R3 / third-audit hardening**: The simulation boot root
    passes the boot-safety predicate.  Discharged by `decide` on the
    five-element fold over the single-mapping table. -/
theorem simBootVSpaceRoot_bootSafe :
    SeLe4n.Platform.RPi5.VSpaceBoot.bootSafeVSpaceRoot simBootVSpaceRoot := by
  unfold SeLe4n.Platform.RPi5.VSpaceBoot.bootSafeVSpaceRoot
    SeLe4n.Platform.RPi5.VSpaceBoot.VSpaceRootWellFormed
    SeLe4n.Platform.RPi5.VSpaceBoot.VSpaceRootWxCompliant
    SeLe4n.Platform.RPi5.VSpaceBoot.VSpaceRootPaddrBounded
    SeLe4n.Platform.RPi5.VSpaceBoot.VSpaceRootVaddrCanonical
    simBootVSpaceRoot simBootPerms
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- asid = 0 ≤ maxAsidValue
    show (0 : Nat) ≤ maxAsidValue
    unfold maxAsidValue; omega
  · -- W^X compliance over the single mapping
    decide
  · -- non-empty mappings
    decide
  · -- paddr < 2^44
    decide
  · -- vaddr canonical (0x1000 < 2^48)
    decide

/-- **WS-RC R3**: The simulation boot root passes the runtime-decidable
    boot-safety check (Bool form). -/
theorem simBootVSpaceRoot_bootSafeCheck :
    SeLe4n.Platform.RPi5.VSpaceBoot.bootSafeVSpaceRootCheck simBootVSpaceRoot = true :=
  (SeLe4n.Platform.RPi5.VSpaceBoot.bootSafeVSpaceRootCheck_iff _).mpr
    simBootVSpaceRoot_bootSafe

/-- **WS-RC R3**: The simulation boot root's `mappings` table satisfies
    `invExt`.  Single insertion preserves `invExt` from the empty
    base. -/
theorem simBootVSpaceRoot_mappings_invExt :
    simBootVSpaceRoot.mappings.invExt := by
  unfold simBootVSpaceRoot
  exact RHTable.insert_preserves_invExt _ _ _ (RHTable.empty_invExt 16 (by omega))

/-- **WS-RC R3**: The simulation `BootVSpaceRootEntry`. -/
def simBootVSpaceRootEntry : SeLe4n.Platform.BootVSpaceRootEntry where
  id := simBootVSpaceRootObjId
  root := simBootVSpaceRoot
  hMappings := simBootVSpaceRoot_mappings_invExt

/-- Marker type for the simulation platform. -/
structure SimPlatform where
  deriving Repr

/-- Simulation machine configuration: idealized 64-bit ARM64 parameters.
    U8-A/U-L16: Memory map uses the shared `simSubstantiveMemoryMap` definition
    from `RuntimeContract.lean` to eliminate duplication.
    AJ-L11: `physicalAddressWidth := 52` intentionally diverges from RPi5's
    44-bit PA width (Board.lean:122). The simulation platform uses the maximum
    ARMv8-A PA width to avoid false negatives in address validation tests.
    RPi5-specific PA bounds checking uses `Board.bcm2712PhysicalAddressWidth`
    (44 bits) via the RPi5 platform contract. -/
def simMachineConfig : SeLe4n.MachineConfig :=
  {
    registerWidth := 64
    virtualAddressWidth := 48
    physicalAddressWidth := 52
    pageSize := 4096
    maxASID := 65536
    memoryMap := simSubstantiveMemoryMap
  }

/-- The simulation platform binding instance.

    **WS-RC R3 (DEEP-BOOT-01)**: `bootVSpaceRoot` is populated with the
    simulation's minimal boot entry (`simBootVSpaceRootEntry`) so the
    sim platform exercises the same `installBootVSpaceRoot` path as
    RPi5.  Per audit plan §7.4 R3.5, Option A "for parity": ~30
    lines of new code defining a minimal VSpaceRoot satisfying
    `bootSafeVSpaceRoot`. -/
instance simPlatformBinding : SeLe4n.Platform.PlatformBinding SimPlatform where
  name := "Simulation (permissive)"
  machineConfig := simMachineConfig
  runtimeContract := simRuntimeContractPermissive
  bootContract := simBootContract
  interruptContract := simInterruptContract
  bootVSpaceRoot := some simBootVSpaceRootEntry

/-- S5-D: Marker type for the simulation restrictive (substantive) platform. -/
structure SimRestrictivePlatform where
  deriving Repr

/-- S5-D: Simulation restrictive platform binding with substantive contracts.

Uses `simRuntimeContractSubstantive` which mirrors RPi5 contract structure:
- Timer monotonicity validated (substantive, not vacuous)
- Memory access restricted to 256 MiB RAM region
- Register writes denied (enables proof hooks)

This platform variant catches contract-level bugs in simulation that would
otherwise only surface on hardware. Test harnesses using this binding exercise
the same contract validation logic as the RPi5 production platform. -/
instance simRestrictivePlatformBinding :
    SeLe4n.Platform.PlatformBinding SimRestrictivePlatform where
  name := "Simulation (substantive-restrictive)"
  machineConfig := simMachineConfig
  runtimeContract := simRuntimeContractSubstantive
  bootContract := simBootContract
  interruptContract := simInterruptContract
  -- WS-RC R3 (DEEP-BOOT-01): same boot VSpaceRoot as the permissive
  -- sim binding — the boot pipeline doesn't depend on which sim
  -- runtime contract is in effect.
  bootVSpaceRoot := some simBootVSpaceRootEntry

/-- U8-A/U-L16: Compile-time consistency theorem proving that the
    `simSubstantiveMemoryMap` used in `RuntimeContract.lean` is identical to
    `simMachineConfig.memoryMap`. This eliminates the risk of the two memory
    map definitions drifting out of sync — any change to either side will
    cause this proof to fail at build time. -/
theorem simSubstantiveMemoryMap_eq_machineConfig :
    simSubstantiveMemoryMap = simMachineConfig.memoryMap := by rfl

end SeLe4n.Platform.Sim
