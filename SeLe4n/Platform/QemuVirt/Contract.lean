-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.Contract
import SeLe4n.Platform.QemuVirt.Board
import SeLe4n.Platform.RPi5.RuntimeContract
import SeLe4n.Platform.RPi5.VSpaceBoot

/-!
# QEMU `virt` — platform binding (WS-BP BP8.1)

The `PlatformBinding` the Lean-linked `virt` image boots under.  It is the
Raspberry Pi 5's binding with the board's address map changed and nothing
else: four Cortex-A76 PEs in one inner-shareable cluster, the confined
two-domain labeling at the same boundary and witnesses, and a kernel boot root
that identity-maps this board's kernel image and devices.

Two pieces are **shared** with the RPi5 binding rather than copied, because
neither reads a board constant: the runtime contract
(`RPi5.rpi5RuntimeContract`, whose memory predicate reads the *installed*
map, `st.machine.memoryMap`) and the kernel boot root's builder and checks
(`RPi5.VSpaceBoot.insertIdentity`, `bootSafeVSpaceRootCheck`).  The boot and
interrupt contracts are this board's, because they read its SPI count.
-/

namespace SeLe4n.Platform.QemuVirt

open SeLe4n.Platform.RPi5.VSpaceBoot

/-- Marker type for the QEMU `virt` platform. -/
structure QemuVirtPlatform where
  deriving Repr

/-- The kernel's text base in the model boot root: `_start`, at the RAM base
    plus the Image header's `text_offset` (`0x8_0000`), where QEMU loads the
    image and the derived link script puts `ORIGIN(RAM)`. -/
def qemuVirtKernelTextBase : SeLe4n.PAddr := SeLe4n.PAddr.ofNat (qemuVirtRamBase + 0x8_0000)

/-- The kernel's data base in the model boot root — the text base plus the
    RPi5 layout's `kernelTextSize`. -/
def qemuVirtKernelDataBase : SeLe4n.PAddr :=
  SeLe4n.PAddr.ofNat (qemuVirtKernelTextBase.toNat + kernelTextSize)

/-- The kernel stack base in the model boot root. -/
def qemuVirtKernelStackBase : SeLe4n.PAddr := SeLe4n.PAddr.ofNat (qemuVirtRamBase + 0x20_0000)

/-- The `virt` kernel boot root: ASID 0, six identity mappings — kernel text
    RX, data RW, stack RW, and the PL011, the GIC distributor and the GIC CPU
    interface as device memory — built with the RPi5 root's own builder. -/
def qemuVirtBootVSpaceRoot : SeLe4n.Model.VSpaceRoot :=
  emptyBootRoot
    |> (insertIdentity · qemuVirtKernelTextBase permsTextRX)
    |> (insertIdentity · qemuVirtKernelDataBase permsDataRW)
    |> (insertIdentity · qemuVirtKernelStackBase permsDataRW)
    |> (insertIdentity · qemuVirtUartBase permsMmioRW)
    |> (insertIdentity · qemuVirtGicDistributorBase permsMmioRW)
    |> (insertIdentity · qemuVirtGicCpuInterfaceBase permsMmioRW)

/-- The boot root's mapping table satisfies `invExt` — six inserts into an
    empty table. -/
theorem qemuVirtBootVSpaceRoot_mappings_invExt : qemuVirtBootVSpaceRoot.mappings.invExt := by
  unfold qemuVirtBootVSpaceRoot insertIdentity emptyBootRoot
  exact SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ <|
        SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ <|
        SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ <|
        SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ <|
        SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ <|
        SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ <|
        SeLe4n.Kernel.RobinHood.RHTable.empty_invExt 16 (by omega)

/-- The boot root passes the kernel boot root's safety check. -/
theorem qemuVirtBootVSpaceRoot_bootSafeCheck :
    bootSafeVSpaceRootCheck qemuVirtBootVSpaceRoot = true := by
  decide

/-- The reserved id of the `virt` boot root — `1`, the smallest non-sentinel
    id, as on the RPi5, so the deployment's object layout is the same on both
    boards. -/
def qemuVirtBootVSpaceRootObjId : SeLe4n.ObjId := SeLe4n.ObjId.ofNat 1

/-- The binding's boot root entry. -/
def qemuVirtBootVSpaceRootEntry : SeLe4n.Platform.BootVSpaceRootEntry where
  id := qemuVirtBootVSpaceRootObjId
  root := qemuVirtBootVSpaceRoot
  hMappings := qemuVirtBootVSpaceRoot_mappings_invExt

/-- The index the untrusted domain begins at — the deployment's labeling
    boundary. -/
def qemuVirtUpperDomainBase : Nat := 0x10_0000

/-- The lower separation witness: `2`, the first slot the boot root leaves
    free, below the boundary and the idle-thread slots. -/
def qemuVirtLowerWitnessIndex : Nat := 2

theorem qemuVirtLowerWitnessIndex_admissible :
    SeLe4n.Kernel.separationWitnessAdmissible ⟨qemuVirtLowerWitnessIndex⟩ = true := by
  decide

theorem qemuVirtLowerWitnessIndex_below_boundary :
    qemuVirtLowerWitnessIndex < SeLe4n.Kernel.separationBoundary qemuVirtUpperDomainBase := by
  decide

/-- The idle threads and the boot root sit below the boundary. -/
theorem qemuVirtUpperDomainBase_clears_boot :
    SeLe4n.Kernel.idleThreadIdBase + SeLe4n.Kernel.Concurrency.numCores ≤ qemuVirtUpperDomainBase ∧
    qemuVirtBootVSpaceRootObjId.toNat < qemuVirtUpperDomainBase := by
  decide

/-- The `virt` boot contract: the object store is empty at boot, and the
    interrupt range fits the GICv2's 1020 INTIDs. -/
def qemuVirtBootContract : SeLe4n.Kernel.Architecture.BootBoundaryContract :=
  { objectTypeMetadataConsistent := (default : SeLe4n.Model.SystemState).objects.size = 0
    objectStoreEmptyAtBoot := (default : SeLe4n.Model.SystemState).objects.size = 0
    irqRangeValid := qemuVirtGicSpiCount + 32 ≤ 1020 }

/-- The `virt` interrupt contract: INTIDs `0 … 287`, and a supported line's
    handler must be registered. -/
def qemuVirtInterruptContract : SeLe4n.Kernel.Architecture.InterruptBoundaryContract :=
  { irqLineSupported := fun irq => irq.toNat < qemuVirtGicSpiCount + 32
    irqHandlerMapped := fun st irq =>
      irq.toNat < qemuVirtGicSpiCount + 32 → st.irqHandlers[irq]? ≠ none
    irqLineSupportedDecidable := by intro irq; infer_instance
    irqHandlerMappedDecidable := by intro st irq; infer_instance }

/-- The QEMU `virt` platform binding. -/
instance qemuVirtPlatformBinding : SeLe4n.Platform.PlatformBinding QemuVirtPlatform where
  name := "QEMU virt (GICv2 / Cortex-A76 / ARM64)"
  machineConfig := qemuVirtMachineConfig
  runtimeContract := SeLe4n.Platform.RPi5.rpi5RuntimeContract
  bootContract := qemuVirtBootContract
  interruptContract := qemuVirtInterruptContract
  bootVSpaceRoot := some qemuVirtBootVSpaceRootEntry
  coreCount := 4
  coreCountPos := by decide
  coreCountLe := by decide
  declaredCoreCountAgrees := by decide
  bindMachineConfig_declaredCoreCount := fun _ => rfl
  bootCoreId := ⟨0, by decide⟩
  sharingDomain := .inner
  deploymentLabeling :=
    SeLe4n.Kernel.confinedDeploymentLabeling qemuVirtUpperDomainBase qemuVirtLowerWitnessIndex
      qemuVirtLowerWitnessIndex_admissible qemuVirtLowerWitnessIndex_below_boundary
  witnessesOffBootVSpaceRoot := by decide

/-- The binding installs its own machine configuration for every account — a
    fixed configuration, so the account selects nothing. -/
theorem qemuVirt_bindMachineConfig (board : SeLe4n.MachineConfig) :
    SeLe4n.Platform.PlatformBinding.bindMachineConfig (platform := QemuVirtPlatform) board =
      qemuVirtMachineConfig := rfl

/-- The binding declares every model core. -/
theorem qemuVirt_cores_eq_allCores :
    SeLe4n.Platform.PlatformBinding.declaredCores (platform := QemuVirtPlatform) =
      SeLe4n.Kernel.Concurrency.allCores :=
  SeLe4n.Platform.PlatformBinding.declaredCores_eq_allCores_of_full rfl

/-- What the `virt` boot installs as its labeling: the confined production
    context at this deployment's boundary. -/
theorem qemuVirt_deploymentLabeling :
    SeLe4n.Platform.PlatformBinding.labeling (platform := QemuVirtPlatform) =
      SeLe4n.Kernel.confinedLabelingContext qemuVirtUpperDomainBase qemuVirtLowerWitnessIndex
        qemuVirtLowerWitnessIndex_admissible qemuVirtLowerWitnessIndex_below_boundary := rfl

/-- The witnesses the `virt` boot declares. -/
theorem qemuVirt_deploymentLabeling_separatedThreads :
    (SeLe4n.Platform.PlatformBinding.labeling (platform := QemuVirtPlatform)).separatedThreads =
      some (⟨qemuVirtLowerWitnessIndex⟩, ⟨qemuVirtUpperDomainBase⟩) := by
  decide

end SeLe4n.Platform.QemuVirt
