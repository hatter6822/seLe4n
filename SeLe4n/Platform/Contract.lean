-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.Assumptions
import SeLe4n.Model.Object.Structures
-- WS-SM SM0.G: SharingDomain comes from the SM0.F foundational types
-- module so the typeclass field can name it without copying the
-- definition into the Platform namespace.
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Kernel.InformationFlow.Policy

/-!
# Platform Binding Contract (H3 preparation)

This module defines the `PlatformBinding` typeclass — the formal interface that
any hardware platform must satisfy to instantiate the seLe4n kernel. A platform
binding bundles:

1. **MachineConfig** — architectural constants (register width, page size, ASID
   limits, physical memory map).
2. **RuntimeBoundaryContract** — decidable predicates on timer monotonicity,
   register context stability, and memory access permissions.
3. **BootBoundaryContract** — propositions about initial object-store and
   capability-ref consistency.
4. **InterruptBoundaryContract** — predicates on supported IRQ lines and handler
   mappings.

## Design rationale

The typeclass approach makes platform selection a type parameter rather than a
value parameter. Kernel transitions remain platform-agnostic (they do not
mention any `PlatformBinding` instance). Only architecture-adapter entrypoints
and test harnesses instantiate a concrete platform.

## Current instantiations

- `SeLe4n.Platform.Sim.simPlatformBinding` — simulation target for trace
  harness and test execution. Defines permissive contracts parallel to
  `SeLe4n.Testing.RuntimeContractFixtures` (functionally equivalent but
  organized under the Platform namespace).
- `SeLe4n.Platform.Sim.simRestrictivePlatformBinding` — S5-D: simulation
  restrictive target with substantive contracts mirroring RPi5 structure
  (timer monotonicity, RAM-bounded memory access, deny register writes).
  Catches contract-level bugs in simulation before hardware bring-up.
- `SeLe4n.Platform.RPi5.rpi5PlatformBinding` — Raspberry Pi 5 (BCM2712/ARM64)
  stub for H3 hardware binding.
-/

namespace SeLe4n.Platform

open SeLe4n.Kernel.Architecture
open SeLe4n.Model

/-- **WS-RC R3 (DEEP-BOOT-01)**: Boot VSpaceRoot entry threaded through
    `PlatformConfig.bootVSpaceRoot` and `PlatformBinding.bootVSpaceRoot`.

    Carries the ObjId at which the boot VSpace will be installed, the
    VSpaceRoot itself, and the `mappings.invExt` proof obligation that
    `installBootVSpaceRoot` (defined in `Platform.Boot`) consumes when
    threading the root through the builder.

    Distinct from `Platform.Boot.ObjectEntry` because the boot VSpaceRoot
    has special `asidTable` registration semantics — handled by
    `installBootVSpaceRoot` rather than the standard `createObject`
    builder.  Lifted to `Platform.Contract` so platform bindings can
    expose the optional boot root via the typeclass without pulling in
    the heavy `Platform.Boot` dependency. -/
structure BootVSpaceRootEntry where
  id : SeLe4n.ObjId
  root : VSpaceRoot
  hMappings : root.mappings.invExt

/-- A complete platform binding bundles all architecture-boundary contracts
    together with the platform's machine configuration.

    Platform implementors provide an instance of this class. Kernel code
    never depends on a specific instance — it is parameterized over the
    typeclass when adapter operations need platform-specific contracts. -/
class PlatformBinding (platform : Type) where
  /-- Platform name used for diagnostics and trace output. -/
  name : String
  /-- Hardware architectural parameters. -/
  machineConfig : SeLe4n.MachineConfig
  /-- Runtime boundary contract governing timer, register, and memory access. -/
  runtimeContract : RuntimeBoundaryContract
  /-- Boot-time boundary contract governing initial state consistency. -/
  bootContract : BootBoundaryContract
  /-- Interrupt routing contract governing IRQ line support and handler mapping. -/
  interruptContract : InterruptBoundaryContract
  /-- **WS-RC R3 (DEEP-BOOT-01)**: Optional canonical boot VSpaceRoot.
      Platforms with a hardware-specific identity-mapped boot VSpace
      (RPi5: `rpi5BootVSpaceRoot`) populate this with an entry.  The
      simulation platform also populates it with `simBootVSpaceRoot`
      (a minimal single-mapping root) for parity with the RPi5
      hardware path, so the trace harness exercises the same
      `installBootVSpaceRoot` code path.

      When set, `Platform.Boot.bootFromPlatformChecked` threads the
      entry through `installBootVSpaceRoot` after the standard
      `initialObjects` fold, registering the VSpace's ASID in
      `asidTable` so subsequent VSpace operations can resolve it.

      The default `none` is kept on the typeclass field for
      compatibility with future bare-metal platforms that boot in
      EL3/SECURE mode without an MMU; current production bindings
      (RPi5, sim) all override the default. -/
  bootVSpaceRoot : Option BootVSpaceRootEntry := none
  /-- **WS-SM SM0.G**: number of cores the platform exposes.

      Multi-core (SMP) coordination in WS-SM phases SM1..SM10
      derives every per-core enumeration / iteration loop / lock
      partition from this single value.  Bindings supply the
      numeric value here; the SM0.E `Concurrency.Types.numCores`
      constant is pinned to the RPi5 binding's `coreCount` via the
      `numCores_eq_rpi5_coreCount` theorem in
      `Platform.RPi5.Contract`. -/
  coreCount : Nat
  /-- **WS-SM SM0.G**: positivity witness for `coreCount`.  Required
      because every consumer (bootCoreId, allCores enumeration,
      `Fin coreCount` typed identifiers) needs at least one core to
      inhabit `Fin coreCount`. -/
  coreCountPos : coreCount > 0
  /-- **WS-SM SM0.G**: the boot core id, scoped to `Fin coreCount`
      so it is structurally in-range.  Always `0` in practice
      (PSCI brings up secondaries from `Aff0 = 0`); typeclass-
      supplied so a future multi-platform port that boots on a
      non-zero affinity slot can override it. -/
  bootCoreId : Fin coreCount
  /-- **WS-SM SM0.G**: ARMv8 memory-shareability domain selecting
      the right DSB barrier kind on this platform.  RPi5 BCM2712
      is single-cluster Cortex-A76 (`.inner`); future big.LITTLE /
      multi-cluster targets use `.outer`. -/
  sharingDomain : SeLe4n.Kernel.Concurrency.SharingDomain
  /-- **WS-RR RR5.1**: the deployment's security-domain assignment — the
      **source** of the labeling context this platform's boot installs, bound
      here so that "what a hardware boot installs" is a definite object in the
      tree rather than a sentence about one.  `Platform.FFI.bootAndInitialisePlatform`
      boots under `PlatformBinding.labeling`, the `Kernel.deploymentLabelingContext`
      of this field.

      **Why the source and not the context** (PR #889 review): the constructor
      is what discharges every `LabelingContextValid` obligation
      (`Kernel.deploymentLabelingContext_valid`) — thread/object coherence by
      construction, non-triviality from the declared witness — and the
      boot-time guard decides only non-triviality.  A binding that stored a
      bare `LabelingContext` with a proof the guard admits it could still label
      a thread and its own TCB object incompatibly, and the non-interference
      theorems would silently stop applying to that deployment.  With the
      source stored, admission (`PlatformBinding.labeling_admitted`) and
      validity (`PlatformBinding.labeling_valid`) are theorems of every
      binding, present and future, rather than obligations each one carries.

      The RPi5 binding supplies the confined two-domain production labeling
      (`Kernel.confinedDeploymentLabeling`); the simulation bindings supply the
      harness labeling (`Kernel.harnessDeploymentLabeling`), under which every
      fixture id sits in one domain. -/
  deploymentLabeling : SeLe4n.Kernel.DeploymentLabeling

/-- Extract the runtime contract from a platform binding instance. -/
@[inline] def PlatformBinding.runtime [PlatformBinding platform] : RuntimeBoundaryContract :=
  PlatformBinding.runtimeContract (platform := platform)

/-- Extract the boot contract from a platform binding instance. -/
@[inline] def PlatformBinding.boot [PlatformBinding platform] : BootBoundaryContract :=
  PlatformBinding.bootContract (platform := platform)

/-- Extract the interrupt contract from a platform binding instance. -/
@[inline] def PlatformBinding.interrupt [PlatformBinding platform] : InterruptBoundaryContract :=
  PlatformBinding.interruptContract (platform := platform)

/-- Extract the machine configuration from a platform binding instance. -/
@[inline] def PlatformBinding.config [PlatformBinding platform] : SeLe4n.MachineConfig :=
  PlatformBinding.machineConfig (platform := platform)

/-- **WS-RC R3 (DEEP-BOOT-01)**: Extract the optional boot VSpaceRoot
    entry from a platform binding instance. -/
@[inline] def PlatformBinding.bootVSpace [PlatformBinding platform] :
    Option BootVSpaceRootEntry :=
  PlatformBinding.bootVSpaceRoot (platform := platform)

/-- **WS-SM SM0.G**: extract the platform's core count.  Wrapper
    `def` so consumers can write `PlatformBinding.cores (platform := P)`
    without the verbose `coreCount`. -/
@[inline] def PlatformBinding.cores [PlatformBinding platform] : Nat :=
  PlatformBinding.coreCount (platform := platform)

/-- **WS-SM SM0.G**: extract the platform's boot core id, typed as
    `Fin (cores platform)`. -/
@[inline] def PlatformBinding.bootCore [PlatformBinding platform] :
    Fin (PlatformBinding.coreCount (platform := platform)) :=
  PlatformBinding.bootCoreId (platform := platform)

/-- **WS-RR RR5.1**: the labeling context the platform's boot installs — the
    constructor's output on the binding's `DeploymentLabeling`. -/
@[inline] def PlatformBinding.labeling [PlatformBinding platform] :
    SeLe4n.Kernel.LabelingContext :=
  SeLe4n.Kernel.deploymentLabelingContext (PlatformBinding.deploymentLabeling (platform := platform))

/-- **WS-RR RR5.1**: every binding's labeling is admitted by the boot-time
    fail-closed guard — a theorem of the constructor, not an obligation the
    binding carries (`isInsecureDefaultContext_deploymentLabelingContext`). -/
theorem PlatformBinding.labeling_admitted [PlatformBinding platform] :
    SeLe4n.Kernel.isInsecureDefaultContext (PlatformBinding.labeling (platform := platform))
      = false :=
  SeLe4n.Kernel.isInsecureDefaultContext_deploymentLabelingContext _

/-- PR #889 review round 3: the cores the binding **declares**, as model core
    ids — the first `coreCount` of `allCores` (`cores` is the count itself).  What the checked platform boot
    installs idle threads on (`bootFromPlatformCheckedWithIdleThreadsFor`), so
    a single-core binding boots a single idle thread; on the full core count
    this is `allCores` (`declaredCores_eq_allCores_of_full`). -/
def PlatformBinding.declaredCores [PlatformBinding platform] :
    List SeLe4n.Kernel.Concurrency.CoreId :=
  SeLe4n.Kernel.Concurrency.allCores.filter
    (fun c => decide (c.val < PlatformBinding.coreCount (platform := platform)))

/-- PR #889 review round 3: a binding declaring every model core declares
    `allCores` — the bridge from the declared-list boot to the all-cores theorems. -/
theorem PlatformBinding.declaredCores_eq_allCores_of_full [PlatformBinding platform]
    (h : PlatformBinding.coreCount (platform := platform) = SeLe4n.Kernel.Concurrency.numCores) :
    PlatformBinding.declaredCores (platform := platform) = SeLe4n.Kernel.Concurrency.allCores := by
  unfold PlatformBinding.declaredCores
  rw [h]
  exact List.filter_eq_self.mpr (fun c _ => decide_eq_true c.isLt)

/-- **WS-SM SM0.G**: extract the platform's ARMv8 sharing domain. -/
@[inline] def PlatformBinding.sharing [PlatformBinding platform] :
    SeLe4n.Kernel.Concurrency.SharingDomain :=
  PlatformBinding.sharingDomain (platform := platform)

end SeLe4n.Platform
