-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.Frame
import SeLe4n.Platform.Boot.InitialThreads

/-!
# The records the started boot installs

WS-ZA ZA6.37.  The first kernel entry starts from the state the started boot
installs, so each record the entries carry must hold of it.  The machine's
physical-address width is the configuration's (`applyMachineConfig` is the only
writer of the machine's configured fields, and the idle stores, the starts, the
interrupt-node install and the capability linking keep the machine), and the
checked boot refuses a configuration wider than 52 bits.
-/

namespace SeLe4n.Platform.Boot

open SeLe4n.Model
open SeLe4n.Kernel

/-- The checked boot installs the configuration's physical-address width. -/
theorem bootFromPlatformChecked_ok_physicalAddressWidth (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist) :
    ist.state.machine.physicalAddressWidth = config.machineConfig.physicalAddressWidth := by
  obtain ⟨_, _, hShape⟩ := bootFromPlatformChecked_ok_shape config ist h
  rcases hShape with ⟨_, hEq⟩ | ⟨entry, _, hEq⟩
  · subst hEq
    rw [bootEnableInterruptsOp_physicalAddressWidth_eq]
    exact bootFromPlatform_machine_physicalAddressWidth config
  · subst hEq
    rw [bootEnableInterruptsOp_physicalAddressWidth_eq]
    show (bootFromPlatform config).state.machine.physicalAddressWidth = _
    exact bootFromPlatform_machine_physicalAddressWidth config

/-- **The started boot installs a physical-address width within the VSpace
bundle's bound.** -/
theorem bootFromPlatformCheckedStartedFor_physicalAddressWidthWithinBound
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformCheckedStartedFor cores config = .ok ist) :
    ist.state.physicalAddressWidthWithinBound := by
  obtain ⟨base, started, hBase, hStart, rfl⟩ := bootFromPlatformCheckedStartedFor_ok cores config ist h
  unfold SystemState.physicalAddressWidthWithinBound
  rw [linkBootCapabilities_machine, installIrqNodes_machine,
    startInitialThreads_machine _ _ _ hStart]
  unfold bootFromPlatformCheckedWithIdleThreadsFor at hBase
  cases hB : bootFromPlatformChecked config with
  | error e => rw [hB] at hBase; cases hBase
  | ok ist0 =>
    rw [hB] at hBase
    simp only [Except.bind] at hBase
    split at hBase
    · split at hBase
      · cases hBase
        rw [foldl_storeIdleThread_machine, bootFromPlatformChecked_ok_physicalAddressWidth config ist0 hB]
        exact bootFromPlatformChecked_ok_implies_physicalAddressWidth_bound config ist0 hB
      · cases hBase
    · cases hBase

end SeLe4n.Platform.Boot
