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

/-- A boot-shaped thread waits on no reply and heads no reply-waiter queue. -/
theorem bootTcbShape_replyView_idle {tcb : TCB} (h : bootTcbShape tcb) :
    tcb.replyView = ReplyView.idle := by
  obtain ⟨-, hIpc, -, -, -, -, -, -, -, -, -, hP, hN, hH, hC, -⟩ := h
  have hP' : tcb.replyWaiterPrevCode = 0 := by
    rw [← TCB.optCode_replyWaiterPrev, hP]; rfl
  have hN' : tcb.replyWaiterNextCode = 0 := by
    rw [← TCB.optCode_replyWaiterNext, hN]; rfl
  have hH' : tcb.replyWaitersHeadCode = 0 := by
    rw [← TCB.optCode_replyWaitersHead, hH]; rfl
  unfold TCB.replyView ReplyView.idle
  rw [hP', hN', hH', hC]
  simp only [TCB.blockingServer?_eq, hIpc]

/-- **A state of linked boot shape keeps the reply-waiter queues consistent**:
every thread is boot shaped, so every view is idle and every queue empty. -/
theorem replyWaitersConsistent_of_bootLinkedShape (ist : IntermediateState)
    (h : bootLinkedShape ist) : ist.state.replyWaitersConsistent :=
  SystemState.replyWaitersConsistent_of_idle fun _ _ hv => by
    obtain ⟨t, hO, rfl⟩ := SystemState.tcb_of_replyViews hv
    exact bootTcbShape_replyView_idle ((h.1 _ _ hO).2.2.2.1 t rfl)

/-- **The started boot installs every record the kernel entries carry**
(`kernelRecordsSound`): the object and ASID tables well formed and the VSpace
bundle (the intermediate state's table facts and the proof-layer bundle), the
reply-waiter queues consistent and no fault record outside a parked thread (the
boot shape), and the machine's physical-address width within the bound (the
checked boot's width gate).  Every kernel entry keeps it, so it holds of every
state the kernel reaches. -/
theorem bootFromPlatformCheckedStartedFor_kernelRecordsSound
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (hNodup : cores.Nodup)
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor cores config = .ok ist) :
    ist.state.kernelRecordsSound := by
  have hShape := bootFromPlatformCheckedStartedFor_bootLinkedShape cores hNodup config ist h
  have hB := bootFromPlatformCheckedStartedFor_proofLayerInvariantBundle cores hNodup config ist h
  exact ⟨⟨ist.hAllTables.objects.1, ist.hAllTables.asidTable, hB.2.2.2.2.2.2.1⟩,
    replyWaitersConsistent_of_bootLinkedShape ist hShape,
    bootFromPlatformCheckedStartedFor_faultRecordParked cores hNodup config ist h,
    bootFromPlatformCheckedStartedFor_physicalAddressWidthWithinBound cores config ist h⟩

end SeLe4n.Platform.Boot
