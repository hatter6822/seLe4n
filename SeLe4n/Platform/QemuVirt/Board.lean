-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Machine
import SeLe4n.Platform.Boot.MemoryCoverage

/-!
# QEMU `virt` — board constants (WS-BP BP8.1)

QEMU ships no BCM2712, so the kernel's first executed boot is on the `virt`
machine: the one QEMU machine with PSCI (for the four-core bring-up BP8.2
runs), a GICv2 and a PL011.  This module is the board's address map as the
kernel models it, and it is the Lean half of the HAL's `QEMU_VIRT`
`BoardMap` (`rust/sele4n-hal/src/board.rs`): the Lean suite writes these
constants into `tests/fixtures/boot_map_qemu_virt.expected` and the HAL's
tests under `board_qemu_virt` read them back, so the two sides are compared by
running both rather than by a literal beside a comment.

Every constant is read off QEMU's own device tree for
`-M virt,gic-version=2 -cpu cortex-a76 -smp 4 -m 1G` (QEMU 8.2's
`hw/arm/virt.c` memory map, dumped with `dumpdtb=`), whose relevant nodes are:

| Node | `reg` | `compatible` |
|---|---|---|
| `memory@40000000` | `[0x4000_0000, +1 GiB)` | (`device_type = "memory"`) |
| `pl011@9000000` | `[0x0900_0000, +0x1000)` | `arm,pl011` |
| `intc@8000000` | `[0x0800_0000, +0x1_0000)`, `[0x0801_0000, +0x1_0000)` | `arm,cortex-a15-gic` |

The machine is a fixed configuration: `-m 1G` is the RAM the lane boots with,
and a board account covering more is still this configuration's board
(`machineConfigCovers` asks only that the account cover the RAM declared).
-/

namespace SeLe4n.Platform.QemuVirt

/-- Where `virt` puts DRAM — `hw/arm/virt.c`'s `VIRT_MEM`. -/
def qemuVirtRamBase : Nat := 0x4000_0000

/-- The RAM the deployment declares: `-m 1G`, the size the QEMU lane boots
    with (`scripts/test_qemu.sh`'s `QEMU_MEMORY`). -/
def qemuVirtRamSize : Nat := 0x4000_0000

/-- One past the RAM the deployment declares. -/
def qemuVirtRamTop : Nat := qemuVirtRamBase + qemuVirtRamSize

/-- The end of the kernel's reserved extent — `[qemuVirtRamBase,
    qemuVirtKernelReservedEnd)` holds the image, its stacks, the Lean heap,
    the device tree's window and the boot table-page pool, exactly as
    `[0, 256 MiB)` does on the Raspberry Pi 5.  The HAL's
    `QEMU_VIRT.kernel_reserved_end`, held to this one by the shared fixture. -/
def qemuVirtKernelReservedEnd : Nat := 0x5000_0000

/-- The device window: `[0x0800_0000, 0x0A00_0000)` — the GIC, the PL011 and
    the rest of `virt`'s low peripherals.  The HAL maps exactly this as Device
    memory (`QEMU_VIRT.device_window_base`/`_top`). -/
def qemuVirtDeviceWindowBase : Nat := 0x0800_0000

/-- The device window's size, 32 MiB, both ends 2 MiB aligned. -/
def qemuVirtDeviceWindowSize : Nat := 0x0200_0000

/-- The PL011's register block. -/
def qemuVirtUartBase : SeLe4n.PAddr := SeLe4n.PAddr.ofNat 0x0900_0000

/-- The GICv2 distributor — `intc@8000000`'s first `reg` block. -/
def qemuVirtGicDistributorBase : SeLe4n.PAddr := SeLe4n.PAddr.ofNat 0x0800_0000

/-- The GICv2 CPU interface — `intc@8000000`'s second `reg` block. -/
def qemuVirtGicCpuInterfaceBase : SeLe4n.PAddr := SeLe4n.PAddr.ofNat 0x0801_0000

/-- `virt`'s interrupt lines above the private ones: QEMU's `NUM_IRQS` is 256,
    so the GICv2 carries SPIs 32 … 287. -/
def qemuVirtGicSpiCount : Nat := 256

/-- The deployment's memory map: the RAM and the device window. -/
def qemuVirtMemoryMap : List SeLe4n.MemoryRegion :=
  [ { base := SeLe4n.PAddr.ofNat qemuVirtRamBase, size := qemuVirtRamSize, kind := .ram }
  , { base := SeLe4n.PAddr.ofNat qemuVirtDeviceWindowBase, size := qemuVirtDeviceWindowSize
      kind := .device } ]

/-- The kernel's reserved extent as a region list — what the boot refuses a
    boot untyped over (`Boot.untypedClearOfKernel`). -/
def qemuVirtKernelReserved : List SeLe4n.MemoryRegion :=
  [{ base := SeLe4n.PAddr.ofNat qemuVirtRamBase
     size := qemuVirtKernelReservedEnd - qemuVirtRamBase, kind := .reserved }]

/-- The boot table-page pool's page count — `link.ld`'s
    `BOOT_TABLE_POOL_PAGES`, which the derived `virt` link script keeps. -/
def qemuVirtBootTablePoolPages : Nat := 16

/-- The pool's first page: the last `qemuVirtBootTablePoolPages` pages of the
    reserved extent, where the link script places `.boot_table_pool`. -/
def qemuVirtBootTablePoolBase : Nat :=
  qemuVirtKernelReservedEnd - qemuVirtBootTablePoolPages * 4096

/-- The pool's pages, in address order. -/
def qemuVirtBootTablePool : List SeLe4n.PAddr :=
  (List.range qemuVirtBootTablePoolPages).map
    (fun i => SeLe4n.PAddr.ofNat (qemuVirtBootTablePoolBase + i * 4096))

/-- The `i`-th page of the pool. -/
def qemuVirtBootTablePage (i : Nat) : SeLe4n.PAddr :=
  SeLe4n.PAddr.ofNat (qemuVirtBootTablePoolBase + i * 4096)

/-- The `virt` machine configuration.  The PE is QEMU's `cortex-a76`, whose
    `ID_AA64MMFR0_EL1.PARange` is `0b0010` — 40 bits, as on the BCM2712 — and
    `-smp 4` gives it the RPi5's four PEs, so the model's width is this
    binding's too. -/
def qemuVirtMachineConfig : SeLe4n.MachineConfig :=
  { registerWidth := 64
    virtualAddressWidth := 48
    physicalAddressWidth := 40
    pageSize := 4096
    maxASID := 65536
    memoryMap := qemuVirtMemoryMap
    declaredCoreCount := 4
    kernelReserved := qemuVirtKernelReserved
    bootTablePool := qemuVirtBootTablePool }

/-- The machine configuration is well-formed. -/
theorem qemuVirtMachineConfig_wellFormed : qemuVirtMachineConfig.wellFormed = true := by
  decide

/-- The MMIO windows the kernel programs — each inside the register block the
    device tree declares for that device, which is what
    `deviceTreeCoversMmioRegions` requires.  The GIC windows are the GIC-400's
    architectural sizes (4 KiB distributor, 8 KiB CPU interface), which lie
    inside `virt`'s 64 KiB blocks. -/
def qemuVirtMmioRegions : List SeLe4n.MemoryRegion :=
  [ { base := qemuVirtUartBase,            size := 0x1000, kind := .device }
  , { base := qemuVirtGicDistributorBase,  size := 0x1000, kind := .device }
  , { base := qemuVirtGicCpuInterfaceBase, size := 0x2000, kind := .device } ]

/-- The MMIO windows paired with the device that must be at each — `arm,pl011`
    for the console and `arm,cortex-a15-gic` for the GICv2 (the string QEMU
    writes; `arm,gic-400` is accepted too, the same programming model).
    Derived from `qemuVirtMmioRegions`, so the two cannot name different
    windows. -/
def qemuVirtRequiredMmioWindows : List SeLe4n.Platform.Boot.RequiredMmioWindow :=
  match qemuVirtMmioRegions with
  | uart :: dist :: cpuIf :: _ =>
    [ { region := uart,  compatible := ["arm,pl011"] }
    , { region := dist,  compatible := ["arm,cortex-a15-gic", "arm,gic-400"] }
    , { region := cpuIf, compatible := ["arm,cortex-a15-gic", "arm,gic-400"] } ]
  | _ => []

/-- The required windows are exactly `qemuVirtMmioRegions`, in order. -/
theorem qemuVirtRequiredMmioWindows_regions_eq :
    qemuVirtRequiredMmioWindows.map (·.region) = qemuVirtMmioRegions := by decide

/-- Every MMIO window lies in the device window the memory map declares. -/
theorem qemuVirtMmioRegions_in_deviceWindow :
    qemuVirtMmioRegions.all (fun r =>
      decide (qemuVirtDeviceWindowBase ≤ r.base.toNat) &&
      decide (r.endAddr ≤ qemuVirtDeviceWindowBase + qemuVirtDeviceWindowSize)) = true := by
  decide

/-- The MMIO windows are pairwise disjoint. -/
theorem qemuVirtMmioRegions_pairwiseDisjoint :
    qemuVirtMmioRegions.all (fun r1 => qemuVirtMmioRegions.all fun r2 =>
      r1.base == r2.base || !r1.overlaps r2) = true := by
  decide

/-- The RAM the boot maps after the verified parse — the deployment's RAM
    outside the kernel's reserved extent, `[0x5000_0000, 0x8000_0000)`, in
    `(base, size)` form, as `Platform.FFI.extendBootRamMap` takes it.  One
    region: the RAM begins at the extent's own base, so what is left of it is
    everything above the extent. -/
def qemuVirtBootRamExtensions : List (Nat × Nat) :=
  [(qemuVirtKernelReservedEnd, qemuVirtRamTop - qemuVirtKernelReservedEnd)]

/-- The extension is RAM of the memory map, clear of the reserved extent, and
    ends exactly where the RAM does — so every RAM address outside the extent
    is in it, and nothing else is. -/
theorem qemuVirtBootRamExtensions_exact :
    qemuVirtBootRamExtensions =
      [(qemuVirtKernelReservedEnd, qemuVirtRamBase + qemuVirtRamSize - qemuVirtKernelReservedEnd)] ∧
    qemuVirtRamBase < qemuVirtKernelReservedEnd ∧
    qemuVirtKernelReservedEnd < qemuVirtRamTop := by
  decide

/-- Every extension is 2 MiB aligned at both ends — what the HAL's
    `extend_boot_tables` writes into the gigabyte's level-2 table. -/
theorem qemuVirtBootRamExtensions_aligned :
    qemuVirtBootRamExtensions.all (fun e =>
      e.1 % 0x20_0000 == 0 && (e.1 + e.2) % 0x20_0000 == 0) = true := by
  decide

end SeLe4n.Platform.QemuVirt
