-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.FFI
import SeLe4n.Platform.Boot.NotificationLabels

/-!
# Raspberry Pi 5 — the deployment the hardware boot installs (WS-BP BP3)

`Platform.FFI.bootAndInitialiseRPi5` boots *a configuration*; this module is
that configuration, `rpi5PlatformConfigFor board`, and the proof that it boots
on every board a Raspberry Pi 5 can be.

## What it is

The caller's half of a `PlatformConfig` (BP3.1): the IRQ table and the initial
objects.  The other two fields — the machine configuration and the boot VSpace
root — are the binding's, supplied by `bindPlatformConfig`, so the machine
configuration here is only the *board account* the binding selects a variant
from.  Since WS-BP BP4.4 that account is the firmware's device tree's
(`rpi5PlatformConfigFromDtb_deployment_ok`), so nothing here is stated for one
board: every gate is decided on each of the five variants — and, since WS-BP
BP7.10, stated symbolically over every *admissible* configuration, each variant
cut to whatever first-gigabyte RAM its firmware reports — and every boot
theorem is stated over an arbitrary account.

Two domains, as `confinedDeploymentLabeling` declares them (BP3.4), each with one
initial thread, its CSpace and its own address space (BP3.2):

| Object | Id | Domain |
|---|---|---|
| root task TCB (the lower separation witness) | `2` | boot (`lowTrusted`) |
| root task CNode | `3` | boot |
| root task VSpace (ASID 1; the boot maps the IPC buffer in it) | `4` | boot |
| interrupt notification (every SPI signals it) | `5` | boot |
| untypeds over the board's RAM outside the kernel's extent, one per BP4.6 extension: the first gigabyte's `[256 MiB, lowRamTop)` as the firmware reports it, then — on every board larger than 1 GiB — the DRAM above the gigabyte (the BCM2712's DRAM is contiguous from 0); each stops below its region map, the last below the root server's pages too | `6`, … | boot |
| root server (WS-SX SX5.1): the root task's IPC-buffer frame and its three page tables, built by the boot in the four pages below the last region map; the mapped frame capability at root CNode slot `7`, a derived copy in the TCB's buffer slot | `8`–`11` | boot |
| untrusted initial TCB (the upper separation witness) | `0x10_0000` | untrusted (`highUntrusted`) |
| its CNode | `0x10_0001` | untrusted |
| its VSpace (ASID 2, empty) | `0x10_0002` | untrusted |

Four decisions, each a consequence of a rule elsewhere rather than a choice made
here:

* **The untypeds are the board's RAM minus the kernel's reserved extent** —
  one untyped per region BP4.6 maps (`rpi5RootTaskUntypeds_regions`): WS-BP
  BP7.10 derives them all from the extensions, the first gigabyte's included,
  so the untypeds stop where the firmware's account says the gigabyte's RAM
  stops (the two fixed untypeds that covered `[256 MiB, 1 GiB)` whole would
  have handed the root task memory the firmware keeps).  The boot refuses
  anything else (`untypedPlacementRespected`), and
  `rpi5InitialObjectsFor_covers_ram` is the other direction: no RAM outside the
  reserved extent is left unowned.  That makes the objects a function of the
  variant (`rpi5InitialObjectsFor`), which the device-tree wrapper applies to
  the variant its parse selected.  Only the boot domain holds untypeds: memory
  is authority, and the untrusted domain's share is the boot domain's to
  delegate.
* **No capability crosses the domain boundary.**  `confinedLabelingContext`
  makes the two domains unable to reach each other in either direction; a root
  task holding a capability to the untrusted thread would be a flow the labeling
  exists to forbid.  Each initial thread's CNode names only its own objects.
* **Device interrupts go to the boot domain, SPIs only.**  As in seL4, the boot
  binds no line: the root task holds the IRQControl capability and issues each
  handler itself (`seL4_IRQControl_Get`), binding it to its interrupt
  notification (`seL4_IRQHandler_SetNotification`), whose signal carries the
  handler's badge (`handleInterrupt`).  SGIs are the kernel's inter-processor
  channel and PPIs are per-core (the timer PPI is the kernel's tick); the kernel
  reserves both, so `Get` refuses them as it refuses an active line.
* **Both threads are `.Inactive`**, as `bootSafeTcbCheck` requires of every boot
  thread: the boot installs them and runs neither.  Starting the root task is the
  first thing the booted kernel does for userspace, and it is not a configuration
  fact.

## What is proved

`rpi5BoundPlatformConfigAt_wellFormed` and its siblings discharge every gate
of the checked boot **by evaluation** (BP3.3), on every member of the RAM family
(BP4.4) — `wellFormed` through the transparent duplicate check
(`objectIdsUnique_eq_transparent`), every other gate by `decide`.
`rpi5BoundPlatformConfigAt_boot` is the acceptance statement at a variant: the
checked boot on the binding's cores succeeds, and
`rpi5DeploymentBootStateAt_witnessesInstalled` says it installs both witness
threads.  So `bootAndInitialiseRPi5 (rpi5PlatformConfigFor board)` commits the
state of the variant `board` selects and the labeling, for **every** account
(`bootAndInitialiseRPi5_rpi5PlatformConfigFor`), and the halting boot the entry
reaches never halts on it (`bootAndInitialiseRPi5OrHalt_rpi5PlatformConfigFor`).
-/

namespace SeLe4n.Platform.RPi5

open SeLe4n.Model
open SeLe4n.Platform.Boot
open SeLe4n.Platform.FFI

-- ============================================================================
-- Object ids
-- ============================================================================

/-- The root task's TCB — the labeling's lower separation witness. -/
def rpi5RootTaskTcbId : SeLe4n.ObjId := ⟨rpi5LowerWitnessIndex⟩
/-- The root task's CNode. -/
def rpi5RootTaskCNodeId : SeLe4n.ObjId := ⟨3⟩
/-- The root task's VSpace. -/
def rpi5RootTaskVSpaceId : SeLe4n.ObjId := ⟨4⟩
/-- The notification the root task binds its interrupt handlers to. -/
def rpi5InterruptNotificationId : SeLe4n.ObjId := ⟨5⟩
/-- **WS-BP BP7.10**: the root task's `i`-th untyped — one per region of RAM
    the board has outside the kernel's reserved extent (`rpi5RootTaskUntypeds`).
    Ids `6, 7, …`, below the untrusted domain's boundary and the idle-thread
    slots, so the boot domain holds them. -/
def rpi5RootTaskUntypedId (i : Nat) : SeLe4n.ObjId := ⟨6 + i⟩
/-- **WS-BP BP7.10**: that untyped's slot in the root task's CNode — `5 + i`,
    after the four slots every board has.  The CNode has sixteen; every
    admissible configuration has at most two untypeds
    (`rpi5RootTaskCNodeFor_slotsAddressable`). -/
def rpi5RootTaskUntypedSlot (i : Nat) : SeLe4n.Slot := SeLe4n.Slot.ofNat (5 + i)
/- **Tombstone (WS-BP BP7.10)**: `rpi5RootTaskUntypedLowId` (`6`, `[256 MiB,
   512 MiB)`), `rpi5RootTaskUntypedHighId` (`7`, `[512 MiB, 1 GiB)`),
   `rpi5RootTaskRamUntypedId` (`8 + i`) and `rpi5RootTaskRamUntypedSlot`
   (`7 + i`) are `rpi5RootTaskUntypedId` / `rpi5RootTaskUntypedSlot` above: the
   two fixed first-gigabyte untypeds covered `[256 MiB, 1 GiB)` whole, which a
   real board's firmware does not report, and were retired for one untyped per
   region of the bound map — the first gigabyte's included. -/
/-- The untrusted domain's initial TCB — the labeling's upper separation
    witness. -/
def rpi5UntrustedTcbId : SeLe4n.ObjId := ⟨rpi5UpperDomainBase⟩
/-- The untrusted initial thread's CNode. -/
def rpi5UntrustedCNodeId : SeLe4n.ObjId := ⟨rpi5UpperDomainBase + 1⟩
/-- The untrusted initial thread's VSpace. -/
def rpi5UntrustedVSpaceId : SeLe4n.ObjId := ⟨rpi5UpperDomainBase + 2⟩

/-- The root task's ASID — the first user ASID; the kernel's is 0. -/
def rpi5RootTaskAsid : SeLe4n.ASID := SeLe4n.ASID.ofNat 1
/-- The untrusted initial thread's ASID. -/
def rpi5UntrustedAsid : SeLe4n.ASID := SeLe4n.ASID.ofNat 2

/-- An initial thread's priority — seL4's `seL4_MaxPrio`, which is what its
    initial thread runs at. -/
def rpi5InitialThreadPriority : SeLe4n.Priority := ⟨255⟩

/-- The five members of the family, as a case split every gate below is decided
    over. -/
private theorem rpi5Variants_cases {P : BCM2712Config → Prop}
    (hOne : P { ramSize := 1 * 1024 * 1024 * 1024 })
    (hTwo : P { ramSize := 2 * 1024 * 1024 * 1024 })
    (hFour : P { ramSize := 4 * 1024 * 1024 * 1024 })
    (hEight : P { ramSize := 8 * 1024 * 1024 * 1024 })
    (hSixteen : P { ramSize := 16 * 1024 * 1024 * 1024 }) :
    ∀ v ∈ rpi5Variants, P v := by
  intro v hv
  simp only [rpi5Variants, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption

-- ============================================================================
-- Objects
-- ============================================================================

/-- An initial thread: `.Inactive`, detached, stored under its own id
    (`embeddedIdentitiesMatchSlots`), with its CSpace and address space named.
    Its CSpace root capability carries the root CNode's guard (WS-SX D5): by
    default seL4's root convention for a 16-slot root, a zero guard of 60
    bits.
    Its IPC buffer address is `0`: its address space maps nothing yet, and the
    thread maps a frame for its buffer out of its own memory before it can use
    one. -/
def rpi5InitialThread (id cspace vspace : SeLe4n.ObjId) (guard : UInt64 := 0)
    (guardSize : UInt8 := 60) : TCB :=
  { tid := ⟨id.val⟩
    priority := rpi5InitialThreadPriority
    domain := ⟨0⟩
    spaceCells := SeLe4n.Model.TCB.spaceCellsOfRoot cspace guard guardSize vspace
    ipcBuffer := SeLe4n.VAddr.ofNat 0 }

/-- **WS-BP BP7.11**: the core the untrusted domain's thread runs on — core 1,
    so the two initial threads, one per domain, are started on two cores and
    neither waits on the other's time slice.  The root task is unpinned and so
    starts on the boot core (`determineTargetCore`). -/
def rpi5UntrustedCore : SeLe4n.Kernel.Concurrency.CoreId := ⟨1, by decide⟩

/-- **WS-BP BP7.11**: the untrusted domain's initial thread — pinned to
    `rpi5UntrustedCore`. -/
def rpi5UntrustedThread : TCB :=
  { rpi5InitialThread rpi5UntrustedTcbId rpi5UntrustedCNodeId rpi5UntrustedVSpaceId with
    cpuAffinity := some rpi5UntrustedCore }

/-- A capability to an object with the given rights, unbadged; a CNode
    capability carries its guard (`cnodeGuard`, `cnodeGuardSize`). -/
def rpi5InitialCap (target : SeLe4n.ObjId) (rights : List AccessRight) (guard : UInt64 := 0)
    (guardSize : UInt8 := 0) : Capability :=
  { target := .object target, rights := AccessRightSet.ofList rights, cnodeGuard := guard,
    cnodeGuardSize := guardSize }

/-- An initial CSpace: 16 slots, which the capabilities naming it as a root
    reach through a 60-bit zero guard (seL4's root-CNode convention, the guard
    in the capability), so one level resolves a whole 64-bit CPtr and a
    capability address is its slot number.  Slot 0 is left empty. -/
def rpi5InitialCNode (slots : List (SeLe4n.Slot × Capability)) : CNode :=
  CNode.ofList 4 slots

/-- **WS-ZA ZA6.4**: the scheduling-control capabilities the boot hands the root
    task, one per core, core `c`'s at slot `base + c` — seL4-MCS's boot info
    `schedcontrol` range, the only authority to configure a scheduling
    context's budget and period. -/
def schedControlBootSlots (base : Nat) : List (SeLe4n.Slot × Capability) :=
  (List.range SeLe4n.Kernel.Concurrency.numCores).map fun c =>
    (SeLe4n.Slot.ofNat (base + c), Capability.schedControlOf c)

/-- The first of the root task's scheduling-control slots: the CNode's top
    four, above the untypeds'. -/
def rpi5SchedControlSlotBase : Nat := 12

/-- **WS-ZA ZA6.32**: the root task's interrupt-control slot, below the
    scheduling controls — seL4's boot info `seL4_CapIRQControl`, the only
    authority to issue an interrupt handler (`seL4_IRQControl_Get`). -/
def rpi5IrqControlSlot : Nat := 11

/-- **WS-SX SX6.7**: the root task's service-registry slot — the one
    authority to register, revoke and query a service
    (`Capability.serviceRegistry`).  Slot 0: the sixteen-slot root CNode's
    others hold the task's own objects, its untypeds, the root server's
    frame and tables (`rpi5RootServerFrameSlot` and the three after it), the
    interrupt control and the scheduling controls. -/
def rpi5ServiceRegistrySlot : Nat := 0

/-- An empty user address space on `asid` — what `bootSafeUserVSpaceRootCheck`
    admits — whose top-level table is the `page`-th page of the binding's
    table-page pool (WS-BP BP7.1, `Platform.Boot.bootRootTablesPlaced`). -/
def rpi5InitialVSpace (asid : SeLe4n.ASID) (page : Nat) : VSpaceRoot :=
  { asid := asid, mappings := SeLe4n.Kernel.RobinHood.RHTable.empty 16
    tableBase := some (rpi5BootTablePage page) }

/-- A normal-memory untyped over `[base, base + size)`, with nothing carved. -/
def rpi5InitialUntyped (base size : Nat) : UntypedObject :=
  { regionBase := SeLe4n.PAddr.ofNat base, regionSize := size }

@[simp] theorem rpi5InitialUntyped_base (base size : Nat) :
    (rpi5InitialUntyped base size).regionBase.toNat = base := rfl

@[simp] theorem rpi5InitialUntyped_size (base size : Nat) :
    (rpi5InitialUntyped base size).regionSize = size := rfl

/-- **WS-BP BP4.7, re-derived at BP7.10**: the root task's untypeds — one per
    extension the boot maps (`rpi5BootRamExtensions v`, which is
    `Platform.FFI.extendBootRamMap`'s argument on a board bound to `v`), the
    `i`-th at id `rpi5RootTaskUntypedId i`.  Derived from the extensions rather
    than listed, so the RAM the HAL maps and the RAM the root task owns are one
    list (`rpi5RootTaskUntypeds_regions`) — and since BP7.10 that list is all
    the RAM the configuration declares outside the kernel's extent, the first
    gigabyte's part cut where the board's firmware said it ends.  **WS-UC UC5**:
    each untyped covers its extension below the region map's reservation,
    which the boot hands the HAL for the map (`Platform.FFI.extendBootRamMap`),
    so no untyped covers the map; **WS-SX SX5.1**: and the last one stops below
    the root server's reservation too (`untypedExtentsOf`). -/
def rpi5RootTaskUntypeds (v : BCM2712Config) : List (SeLe4n.ObjId × UntypedObject) :=
  (untypedExtentsOf (rpi5BootRamExtensions v)).mapIdx fun i u =>
    (rpi5RootTaskUntypedId i, rpi5InitialUntyped u.1 u.2)

/-- The untypeds built over any list of parts have exactly those parts —
    stated over the list, so no proof about a configuration's untypeds asks the
    kernel to evaluate that configuration's extensions: with the first region
    sized `lowRamTop - rpi5RamOrigin` (`v0.36.36`), `Nat.sub` would unfold once
    per unit of its literal second argument. -/
private theorem untypedsOver_regions (l : List (Nat × Nat)) :
    (l.mapIdx fun i u => (rpi5RootTaskUntypedId i, rpi5InitialUntyped u.1 u.2)).map
        (fun u => (u.2.regionBase.toNat, u.2.regionSize)) = l := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_mapIdx, rpi5InitialUntyped_base,
      rpi5InitialUntyped_size]

/-- **WS-BP BP4.7, WS-UC UC5, WS-SX SX5.1**: the untypeds' regions are exactly
    the untyped parts of the extensions the boot maps (`untypedExtentsOf`), in
    order — on every configuration. -/
theorem rpi5RootTaskUntypeds_regions (v : BCM2712Config) :
    (rpi5RootTaskUntypeds v).map (fun u => (u.2.regionBase.toNat, u.2.regionSize)) =
      untypedExtentsOf (rpi5BootRamExtensions v) :=
  untypedsOver_regions _

/-- **WS-BP BP7.10**: how many extensions an admissible configuration has — the
    first gigabyte's, and the variant's RAM above it on every board larger than
    the gigabyte.  A function of the RAM size alone, so it is the same at every
    first-gigabyte top. -/
theorem rpi5BootRamExtensions_length (v : BCM2712Config) (hv : v.Admissible) :
    (rpi5BootRamExtensions v).length = if rpi5FirstGigabyteTop < v.ramSize then 2 else 1 := by
  rw [rpi5BootRamExtensions_eq v (rpi5KernelReservedEnd_lt_of_admissible _ hv.2)]
  split <;> rfl

/-- **WS-BP BP7.10**: the root task's CNode slots for `n` untypeds: its own TCB,
    CNode and VSpace, the interrupt notification, and untyped `i` at slot
    `5 + i` (`rpi5RootTaskUntypedSlot`), (WS-SX SX6.7) the service registry at
    `rpi5ServiceRegistrySlot`, (WS-ZA ZA6.32) the interrupt control
    at `rpi5IrqControlSlot`, and (WS-ZA ZA6.4) each core's scheduling control
    from `rpi5SchedControlSlotBase`.  A function of the count, because a
    capability names an object and not its extent. -/
def rpi5RootTaskCNodeSlotsOfCount (n : Nat) : List (SeLe4n.Slot × Capability) :=
  [ (SeLe4n.Slot.ofNat 1, rpi5InitialCap rpi5RootTaskTcbId [.read, .write, .grant, .grantReply])
  , (SeLe4n.Slot.ofNat 2, rpi5InitialCap rpi5RootTaskCNodeId [.read, .write, .grant, .grantReply]
      (guardSize := 60))
  , (SeLe4n.Slot.ofNat 3, rpi5InitialCap rpi5RootTaskVSpaceId [.read, .write])
  , (SeLe4n.Slot.ofNat 4, rpi5InitialCap rpi5InterruptNotificationId [.read, .write]) ] ++
  ((List.range n).map fun i =>
    (rpi5RootTaskUntypedSlot i, rpi5InitialCap (rpi5RootTaskUntypedId i) [.read, .write, .retype])) ++
  [(SeLe4n.Slot.ofNat rpi5ServiceRegistrySlot, Capability.serviceRegistry),
   (SeLe4n.Slot.ofNat rpi5IrqControlSlot, Capability.irqControl)] ++
  schedControlBootSlots rpi5SchedControlSlotBase

/-- The root task's CNode slots on a board bound to `v` — one untyped
    capability per extension. -/
def rpi5RootTaskCNodeSlots (v : BCM2712Config) : List (SeLe4n.Slot × Capability) :=
  rpi5RootTaskCNodeSlotsOfCount (rpi5BootRamExtensions v).length

/-- The root task's CNode on a board bound to `v`, over
    `rpi5RootTaskCNodeSlots v`. -/
def rpi5RootTaskCNodeFor (v : BCM2712Config) : CNode :=
  rpi5InitialCNode (rpi5RootTaskCNodeSlots v)

/-- **WS-BP BP4.7**: every capability the root task's CNode is configured with
    sits at a slot the CNode's radix can address, on every admissible
    configuration — the boot bounds a CNode's slot *count* and not its indices
    (WS-RR RR8.16), so a slot at or above sixteen would be stored and never
    reachable.  An admissible configuration has one or two untypeds
    (`rpi5BootRamExtensions_length`), and both counts are decided. -/
theorem rpi5RootTaskCNodeFor_slotsAddressable (v : BCM2712Config) (hv : v.Admissible) :
    (rpi5RootTaskCNodeSlots v).all
      (fun p => (rpi5RootTaskCNodeFor v).slotAddressable p.1) = true := by
  unfold rpi5RootTaskCNodeFor rpi5RootTaskCNodeSlots
  rw [rpi5BootRamExtensions_length v hv]
  split <;> decide

/-- The untrusted initial thread's CNode: its own TCB, CNode and VSpace, and
    nothing of the boot domain's. -/
def rpi5UntrustedCNode : CNode :=
  rpi5InitialCNode
    [ (SeLe4n.Slot.ofNat 1, rpi5InitialCap rpi5UntrustedTcbId [.read, .write, .grant, .grantReply])
    , (SeLe4n.Slot.ofNat 2, rpi5InitialCap rpi5UntrustedCNodeId [.read, .write, .grant, .grantReply]
      (guardSize := 60))
    , (SeLe4n.Slot.ofNat 3, rpi5InitialCap rpi5UntrustedVSpaceId [.read, .write]) ]

private def tcbEntry (id : SeLe4n.ObjId) (tcb : TCB) : ObjectEntry :=
  { id := id
    obj := .tcb tcb
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => nomatch h }

private def cnodeEntry (id : SeLe4n.ObjId) (cn : CNode) : ObjectEntry :=
  { id := id, obj := .cnode cn
    hSlots := fun _ h => by cases h; exact CNode.slotsUnique_holds _
    hMappings := fun _ h => nomatch h }

private def vspaceEntry (id : SeLe4n.ObjId) (asid : SeLe4n.ASID) (page : Nat) : ObjectEntry :=
  { id := id, obj := .vspaceRoot (rpi5InitialVSpace asid page)
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => by
      cases h; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt 16 (by omega) }

private def untypedEntry (id : SeLe4n.ObjId) (ut : UntypedObject) : ObjectEntry :=
  { id := id
    obj := .untyped ut
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => nomatch h }

@[simp] private theorem untypedEntry_id (id : SeLe4n.ObjId) (ut : UntypedObject) :
    (untypedEntry id ut).id = id := rfl

private def notificationEntry (id : SeLe4n.ObjId) : ObjectEntry :=
  { id := id
    obj := .notification
      { state := .idle, hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero }
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => nomatch h }

/-- **WS-BP BP3.2 / BP4.7 / BP7.10**: the initial objects on a board bound to
    `v` — the seven the deployment has on every board, then the root task's
    untypeds over that board's RAM outside the kernel's extent
    (`rpi5RootTaskUntypeds`).

    **WS-BP BP4.7** made this a function of the configuration, and it has to
    be one: which RAM a board has is what the verified device-tree parse
    decides, so a fixed list either describes less than the board has — RAM the
    boot maps and nobody owns — or describes RAM the board lacks, which
    `untypedPlacementRespected` refuses.  **WS-BP BP7.10** extended that to the
    first gigabyte: its two fixed untypeds covered `[256 MiB, 1 GiB)` whole,
    including the top of the gigabyte a real board's firmware keeps for itself,
    so the root task would have been handed authority to retype VideoCore
    memory.  The device-tree wrapper applies this to the configuration its
    parse selected (`rpi5PlatformConfigFromDtb`'s `initialObjectsFor`). -/
def rpi5InitialObjectsFor (v : BCM2712Config) : List ObjectEntry :=
  [ tcbEntry rpi5RootTaskTcbId
      (rpi5InitialThread rpi5RootTaskTcbId rpi5RootTaskCNodeId rpi5RootTaskVSpaceId)
  , cnodeEntry rpi5RootTaskCNodeId (rpi5RootTaskCNodeFor v)
  , vspaceEntry rpi5RootTaskVSpaceId rpi5RootTaskAsid 0
  , notificationEntry rpi5InterruptNotificationId
  , tcbEntry rpi5UntrustedTcbId rpi5UntrustedThread
  , cnodeEntry rpi5UntrustedCNodeId rpi5UntrustedCNode
  , vspaceEntry rpi5UntrustedVSpaceId rpi5UntrustedAsid 1 ] ++
  (rpi5RootTaskUntypeds v).map fun u => untypedEntry u.1 u.2

/-- **WS-BP BP3.1 / BP4.4**: the RPi5 deployment's configuration on a board
    account — the caller's half.  `bindPlatformConfig` supplies the binding's
    boot VSpace root and binds the machine configuration; `board` is only the
    *account* the binding selects a variant from.  The hardware entry takes it
    from the firmware's device tree (`PlatformConfig.fromDeviceTree`,
    `rpi5PlatformConfigFromDtb_ok_eq_fromDeviceTree`), so the deployment is
    stated over every account rather than over one board. -/
def rpi5PlatformConfigFor (board : SeLe4n.MachineConfig) : PlatformConfig :=
  { initialObjects := rpi5InitialObjectsFor (rpi5VariantFor board)
    machineConfig := board }

/-- **WS-BP BP4.4**: the configuration the hardware boot checks on a board whose
    account selects variant `v` — `bindPlatformConfig` at the RPi5 binding
    (`bindPlatformConfig_rpi5PlatformConfigFor`). -/
def rpi5BoundPlatformConfigAt (v : BCM2712Config) : PlatformConfig :=
  { initialObjects := rpi5InitialObjectsFor v
    machineConfig := rpi5MachineConfigForVariant v
    bootVSpaceRoot := PlatformBinding.bootVSpaceRoot (platform := RPi5Platform)
    initialThreads := PlatformBinding.initialThreads (platform := RPi5Platform)
    initialInterfaces := PlatformBinding.serviceInterfaces (platform := RPi5Platform)
    rootServer := rpi5RootServerAt v }

/-- **WS-BP BP4.4**: binding a board account is choosing a variant — the bound
    configuration depends on the account only through `rpi5VariantFor`. -/
theorem bindPlatformConfig_rpi5PlatformConfigFor (board : SeLe4n.MachineConfig) :
    bindPlatformConfig RPi5Platform (rpi5PlatformConfigFor board) =
      rpi5BoundPlatformConfigAt (rpi5VariantFor board) := rfl

-- ============================================================================
-- WS-BP BP3.3 — every gate of the checked boot, discharged by evaluation on
-- the five family members (BP4.4), and carried to every first-gigabyte top the
-- firmware may report (BP7.10)
-- ============================================================================

/-- **WS-BP BP3.3**: on each family member, the bound configuration is
    well-formed — every conjunct.  The object table's duplicate check runs a
    hash set the kernel cannot reduce, so it is rewritten to its transparent
    form first (`objectIdsUnique_eq_transparent`); everything else is
    `decide`. -/
private theorem member_wellFormed :
    ∀ v ∈ rpi5Variants, (rpi5BoundPlatformConfigAt v).wellFormed = true := by
  apply rpi5Variants_cases <;>
    (unfold PlatformConfig.wellFormed
     rw [objectIdsUnique_eq_transparent]
     decide)

private theorem member_bootSafe :
    ∀ v ∈ rpi5Variants, (rpi5BoundPlatformConfigAt v).initialObjects.all
      (fun entry => bootSafeObjectCheck entry.obj) = true := by
  apply rpi5Variants_cases <;> decide

private theorem member_asidsDistinct :
    ∀ v ∈ rpi5Variants, bootVSpaceAsidsDistinct (rpi5BoundPlatformConfigAt v) = true := by
  apply rpi5Variants_cases <;> decide

private theorem member_rootDistinct :
    ∀ v ∈ rpi5Variants, bootVSpaceRootObjIdDistinct (rpi5BoundPlatformConfigAt v) = true := by
  apply rpi5Variants_cases <;> decide

private theorem member_affinities :
    ∀ v ∈ rpi5Variants,
      bootAffinitiesDeclared (PlatformBinding.declaredCores (platform := RPi5Platform))
        (rpi5BoundPlatformConfigAt v) = true := by
  apply rpi5Variants_cases <;> decide

/-- Two boot entries with one id and one object are one entry — the proof
    fields are propositions. -/
private theorem objectEntry_eq {e₁ e₂ : ObjectEntry} (hId : e₁.id = e₂.id)
    (hObj : e₁.obj = e₂.obj) : e₁ = e₂ := by
  cases e₁; cases e₂; cases hId; cases hObj; rfl

/-- **WS-BP BP7.10**: an admissible configuration's bound deployment agrees with
    its family member's on everything but the untyped extents and the memory
    map (`PlatformConfig.withoutExtents`) — the untypeds are one per extension
    and there are as many at every first-gigabyte top
    (`rpi5BootRamExtensions_length`), and a capability names an object, not its
    extent.  So every gate that does not read an extent holds here because it
    holds on the member. -/
theorem rpi5BoundPlatformConfigAt_withoutExtents (v : BCM2712Config) (hv : v.Admissible) :
    (rpi5BoundPlatformConfigAt v).withoutExtents =
      (rpi5BoundPlatformConfigAt v.uncut).withoutExtents := by
  have hLen : (rpi5BootRamExtensions v).length = (rpi5BootRamExtensions v.uncut).length := by
    rw [rpi5BootRamExtensions_length v hv,
      rpi5BootRamExtensions_length v.uncut (rpi5Variants_admissible _ hv.1)]
    rfl
  have hSlots : rpi5RootTaskCNodeFor v = rpi5RootTaskCNodeFor v.uncut := by
    unfold rpi5RootTaskCNodeFor rpi5RootTaskCNodeSlots
    rw [hLen]
  have hUnt : ((rpi5RootTaskUntypeds v).map fun u => untypedEntry u.1 u.2).map
        ObjectEntry.withoutUntypedExtent =
      ((rpi5RootTaskUntypeds v.uncut).map fun u => untypedEntry u.1 u.2).map
        ObjectEntry.withoutUntypedExtent := by
    apply List.ext_getElem
    · simp [rpi5RootTaskUntypeds, hLen]
    · intro i h₁ h₂
      apply objectEntry_eq
      · simp [rpi5RootTaskUntypeds, untypedEntry_id]
      · simp [rpi5RootTaskUntypeds, ObjectEntry.withoutUntypedExtent, untypedEntry,
          objectWithoutUntypedExtent, untypedWithoutExtent, rpi5InitialUntyped]
  have hRS : (rpi5RootServerAt v).map RootServerReservation.withoutMemory =
      (rpi5RootServerAt v.uncut).map RootServerReservation.withoutMemory :=
    rootServerReservationOf_withoutMemory _ _ hLen _ _ _ _
  unfold PlatformConfig.withoutExtents rpi5BoundPlatformConfigAt rpi5InitialObjectsFor
  simp only [List.map_append, hUnt, hSlots, hRS]
  rfl

/-- **WS-BP BP7.10**: an entry of the deployment that is an untyped is the
    `i`-th root-task untyped, over the `i`-th extension — none of the fixed
    seven objects is an untyped. -/
private theorem untyped_of_mem (v : BCM2712Config) (e : ObjectEntry) (ut : UntypedObject)
    (he : e ∈ rpi5InitialObjectsFor v) (hObj : e.obj = .untyped ut) :
    ∃ (i : Nat) (h : i < (untypedExtentsOf (rpi5BootRamExtensions v)).length),
      e.id = rpi5RootTaskUntypedId i ∧
        ut = rpi5InitialUntyped (untypedExtentsOf (rpi5BootRamExtensions v))[i].1
          (untypedExtentsOf (rpi5BootRamExtensions v))[i].2 := by
  unfold rpi5InitialObjectsFor at he
  rcases List.mem_append.mp he with hFixed | hUnt
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hFixed
    rcases hFixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hObj
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hUnt
    unfold rpi5RootTaskUntypeds at hu
    obtain ⟨i, hi', hEq⟩ := List.mem_mapIdx.mp hu
    refine ⟨i, hi', ?_, ?_⟩
    · rw [← hEq]; rfl
    · have : (untypedEntry u.1 u.2).obj = .untyped u.2 := rfl
      rw [this] at hObj
      cases hObj
      rw [← hEq]

/-- **WS-BP BP7.10**: the extensions of an admissible configuration are pairwise
    disjoint — the first gigabyte's ends at the admissible top, at most the
    gigabyte, where the variant's begins. -/
private theorem extensions_pairwise_disjoint (v : BCM2712Config) (hv : v.Admissible) :
    (rpi5BootRamExtensions v).Pairwise (fun a b => a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1) := by
  have hKre := rpi5KernelReservedEnd_lt_of_admissible _ hv.2
  have hTop := ((rpi5LowRamTopAdmissible_iff _).mp hv.2).2.1
  rw [rpi5BootRamExtensions_eq v hKre]
  split
  · simp only [List.cons_append, List.nil_append]
    exact List.pairwise_pair.mpr (Or.inl (by omega))
  · simp

/-- An untyped over an extension of any machine configuration that reserves
    the kernel's extent is placed: inside the RAM region the extension was cut
    from, and clear of the extent.  Stated over the configuration and the
    extension, not over a board configuration: with the first region sized
    `lowRamTop - rpi5RamOrigin` (`v0.36.36`), evaluating a symbolic board's
    extensions unfolds `Nat.sub` once per unit of the origin. -/
private theorem extension_placed (mc : SeLe4n.MachineConfig)
    (hRes : mc.kernelReserved = rpi5KernelReserved)
    (hDev : ∀ r ∈ mc.memoryMap, r.kind = .ram → ∀ d ∈ mc.kernelDevices, r.endAddr ≤ d.base.toNat)
    (x : Nat × Nat) (hx : x ∈ bootRamExtensionsOf mc.memoryMap) (sz : Nat) (hle : sz ≤ x.2) :
    (untypedWithinDeclaredRegion mc (rpi5InitialUntyped x.1 sz) &&
      untypedClearOfKernel mc (rpi5InitialUntyped x.1 sz) &&
      untypedClearOfKernelDevices mc (rpi5InitialUntyped x.1 sz)) = true := by
  obtain ⟨r, hr, hk, hlo, hend, hkre, _⟩ := mem_bootRamExtensionsOf _ _ hx
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold untypedWithinDeclaredRegion
    refine List.any_eq_true.mpr ⟨r, hr, ?_⟩
    simp only [untypedRegionKind, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      rpi5InitialUntyped_base, rpi5InitialUntyped_size]
    refine ⟨⟨?_, hlo⟩, by omega⟩
    simp [rpi5InitialUntyped, hk]
  · unfold untypedClearOfKernel
    rw [hRes]
    simp only [rpi5KernelReserved, List.all_cons, List.all_nil, Bool.and_true, Bool.or_eq_true,
      decide_eq_true_eq, rpi5InitialUntyped_base, rpi5InitialUntyped_size]
    right
    simpa [SeLe4n.MemoryRegion.endAddr, SeLe4n.PAddr.ofNat, SeLe4n.PAddr.toNat] using hkre
  · unfold untypedClearOfKernelDevices
    refine List.all_eq_true.mpr fun d hd => ?_
    simp only [Bool.or_eq_true, decide_eq_true_eq, rpi5InitialUntyped_base,
      rpi5InitialUntyped_size]
    left
    have := hDev r hr hk d hd
    have hE : x.1 + x.2 ≤ d.base.toNat := by
      simpa [SeLe4n.PAddr.ofNat, SeLe4n.PAddr.toNat, hend] using this
    simp only [SeLe4n.PAddr.toNat] at hE ⊢
    omega

/-- Two untypeds over extensions that do not overlap do not overlap either
    (stated over the extensions, for the reason above). -/
private theorem extensions_disjoint_untyped (a b : Nat × Nat) (sa sb : Nat) (hle : sa ≤ a.2)
    (h : a.1 + a.2 ≤ b.1) :
    (rpi5InitialUntyped a.1 sa).regionBase.val + (rpi5InitialUntyped a.1 sa).regionSize ≤
      (rpi5InitialUntyped b.1 sb).regionBase.val := by
  simp only [rpi5InitialUntyped, SeLe4n.PAddr.ofNat]
  omega

/-- The `i`-th untyped part of an extension list starts at the `i`-th
    extension and lies inside it. -/
private theorem untypedExtentsOf_within (l : List (Nat × Nat)) (i : Nat)
    (h : i < (untypedExtentsOf l).length) :
    (untypedExtentsOf l)[i].1 = (l[i]'(by simpa using h)).1 ∧
      (untypedExtentsOf l)[i].2 ≤ (l[i]'(by simpa using h)).2 := by
  obtain ⟨h1, h2⟩ := untypedExtentsOf_getElem l i h
  exact ⟨h1, Nat.le_trans h2 (untypedSizeOf_le _)⟩

/-- **WS-BP BP7.10**: the one gate the projection forgets, decided over the
    structure rather than by evaluation — every untyped is its extension, which
    lies inside a RAM region of the bound map (`mem_bootRamExtensionsOf`) and
    clear of the kernel's extent, and two distinct untypeds are two distinct
    extensions, which do not overlap. -/
theorem rpi5BoundPlatformConfigAt_placement (v : BCM2712Config) (hv : v.Admissible) :
    untypedPlacementRespected (rpi5BoundPlatformConfigAt v) = true := by
  unfold untypedPlacementRespected
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨?_, ?_⟩
  · intro e he
    cases hObj : e.obj with
    | untyped ut =>
        obtain ⟨i, hi, _, rfl⟩ := untyped_of_mem v e ut he hObj
        obtain ⟨hB, hS⟩ := untypedExtentsOf_within _ i hi
        rw [hB]
        exact extension_placed (rpi5MachineConfigForVariant v) rfl
          (rpi5MemoryMapForConfig_ram_below_devices v hv) _ (List.getElem_mem _) _ hS
    | _ => rfl
  · intro e₁ he₁ e₂ he₂
    unfold untypedEntriesDisjoint
    cases hO₁ : e₁.obj with
    | untyped u₁ =>
        cases hO₂ : e₂.obj with
        | untyped u₂ =>
            obtain ⟨i, hi, hId₁, rfl⟩ := untyped_of_mem v e₁ u₁ he₁ hO₁
            obtain ⟨j, hj, hId₂, rfl⟩ := untyped_of_mem v e₂ u₂ he₂ hO₂
            obtain ⟨hBi, hSi⟩ := untypedExtentsOf_within _ i hi
            obtain ⟨hBj, hSj⟩ := untypedExtentsOf_within _ j hj
            rw [hBi, hBj]
            simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
            have hi' : i < (rpi5BootRamExtensions v).length := by simpa using hi
            have hj' : j < (rpi5BootRamExtensions v).length := by simpa using hj
            by_cases hij : i = j
            · subst hij; exact Or.inl (Or.inl (hId₁.trans hId₂.symm))
            · have hP := List.pairwise_iff_getElem.mp (extensions_pairwise_disjoint v hv)
              rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
              · rcases hP i j hi' hj' hlt with h | h
                · exact Or.inl (Or.inr (extensions_disjoint_untyped _ _ _ _ hSi h))
                · exact Or.inr (extensions_disjoint_untyped _ _ _ _ hSj h)
              · rcases hP j i hj' hi' hgt with h | h
                · exact Or.inr (extensions_disjoint_untyped _ _ _ _ hSj h)
                · exact Or.inl (Or.inr (extensions_disjoint_untyped _ _ _ _ hSi h))
        | _ => rfl
    | _ => rfl

/-- **WS-SX SX5.1**: the last extension of an admissible configuration, with
    the facts the root server's placement reads: its index, that it is RAM of
    the bound map clear of the kernel's extent, that it holds the reservation,
    and that it is whole 2 MiB blocks. -/
private theorem lastExtension_facts (v : BCM2712Config) (hv : v.Admissible) (e : Nat × Nat)
    (hL : (rpi5BootRamExtensions v).getLast? = some e) :
    ∃ (n : Nat) (hn : n < (rpi5BootRamExtensions v).length),
      n + 1 = (rpi5BootRamExtensions v).length ∧ (rpi5BootRamExtensions v)[n] = e ∧
      e ∈ rpi5BootRamExtensions v ∧ rootServerFits e = true ∧
      e.1 % 0x20_0000 = 0 ∧ (e.1 + e.2) % 0x20_0000 = 0 := by
  rw [List.getLast?_eq_getElem?] at hL
  have hlen : (rpi5BootRamExtensions v).length - 1 < (rpi5BootRamExtensions v).length := by
    rcases Nat.eq_zero_or_pos (rpi5BootRamExtensions v).length with h0 | hpos
    · rw [List.getElem?_eq_none (by omega)] at hL; cases hL
    · omega
  rw [List.getElem?_eq_getElem hlen] at hL
  have hEq := Option.some.inj hL
  have hMem : e ∈ rpi5BootRamExtensions v := hEq ▸ List.getElem_mem hlen
  have hAcc := List.all_eq_true.mp (rpi5BootRamExtensions_admissible v hv) e hMem
  have hFit := rootServerFits_of_accepted e hAcc
  unfold rpi5BootRamExtensionAccepted at hAcc
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hAcc
  obtain ⟨⟨⟨⟨⟨_, hBase⟩, hEnd⟩, _⟩, _⟩, _⟩ := hAcc
  exact ⟨_, hlen, by omega, hEq, hMem, hFit, hBase, hEnd⟩

/-- **WS-SX SX5.1**: the root server's pages are placed on every admissible
    configuration — whole pages inside the RAM region its extension was cut
    from, directly above the last untyped and below that extension's region
    map, so clear of every untyped (the others are other extensions, which do
    not overlap), of the kernel's extent and devices, and of every region map.
    Decided over the structure, as the untyped placement is. -/
private theorem paddr_toNat_ofNat (n : Nat) : (SeLe4n.PAddr.ofNat n).toNat = n := rfl

private theorem rootServerMemoryPlaced_over (v : BCM2712Config) (hv : v.Admissible)
    (c : PlatformConfig) (hMap : c.machineConfig.memoryMap = rpi5MemoryMapForConfig v)
    (hRes : c.machineConfig.kernelReserved = rpi5KernelReserved)
    (hDevs : c.machineConfig.kernelDevices = mmioRegions)
    (hObjs : c.initialObjects = rpi5InitialObjectsFor v) (rs : RootServerReservation) (e : Nat × Nat)
    (hL : (rpi5BootRamExtensions v).getLast? = some e)
    (hBase : rs.base.toNat = rootServerBaseOf e) (hExts : rs.ramExtensions = rpi5BootRamExtensions v) :
    rootServerMemoryPlaced c rs = true := by
    obtain ⟨n, hn, hn1, hEn, hMem, hFit, hB2, hE2⟩ := lastExtension_facts v hv e hL
    obtain ⟨hU0, hUb, hRm, hTop⟩ := rootServer_tiles e hFit
    have hPg := regionMapReserveBytes_pages e.2
    obtain ⟨r, hr, hk, hlo, hend, hkre, _⟩ := mem_bootRamExtensionsOf _ _ hMem
    have hDev := rpi5MemoryMapForConfig_ram_below_devices v hv r hr hk
    have hRB : rootServerReserveBytes = 16384 := rfl
    have hRmB : regionMapBaseOf e ≥ e.1 := by unfold regionMapBaseOf; omega
    have hP := List.pairwise_iff_getElem.mp (extensions_pairwise_disjoint v hv)
    -- every other extension lies wholly below or above `e`
    have hOther : ∀ j (hj : j < (rpi5BootRamExtensions v).length), j ≠ n →
        (rpi5BootRamExtensions v)[j].1 + (rpi5BootRamExtensions v)[j].2 ≤ e.1 ∨
          e.1 + e.2 ≤ (rpi5BootRamExtensions v)[j].1 := by
      intro j hj hjn
      have hjlt : j < n := by omega
      rcases hP j n hj hn hjlt with h | h
      · rw [hEn] at h; exact Or.inl h
      · rw [hEn] at h; exact Or.inr h
    unfold rootServerMemoryPlaced
    simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq,
      decide_eq_true_eq, hMap, hRes, hDevs, hObjs, hBase, hExts]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · -- page aligned
      unfold SeLe4n.pageBytes at hPg ⊢
      rw [hRB] at hRm
      omega
    · -- inside the RAM region the extension was cut from
      refine ⟨r, hr, ⟨hk, ?_⟩, ?_⟩
      · omega
      · omega
    · -- clear of every untyped
      intro ent hent
      cases hObj : ent.obj with
      | untyped ut =>
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        obtain ⟨i, hi, _, rfl⟩ := untyped_of_mem v ent ut hent hObj
        have hi' : i < (rpi5BootRamExtensions v).length := by simpa using hi
        -- `rw`, not `simp`: the two are `rfl` lemmas, and a `simp` by them is
        -- checked by the kernel unfolding the extensions' closed form.
        rw [rpi5InitialUntyped_base, rpi5InitialUntyped_size, untypedExtentsOf_getElem_eq _ i hi']
        by_cases hin : i = n
        · subst hin
          rw [if_pos hn1, hEn]
          right
          unfold untypedExtentBelowRootServerOf at hUb ⊢
          simp only at hUb ⊢
          omega
        · rw [if_neg (by omega)]
          simp only [untypedExtentOf_fst, untypedExtentOf_snd]
          have hle := untypedSizeOf_le (rpi5BootRamExtensions v)[i].2
          rcases hOther i hi' hin with h | h
          · right; omega
          · left; omega
      | _ => rfl
    · -- clear of the kernel's reserved extent
      intro k hk'
      simp only [rpi5KernelReserved, List.mem_cons, List.not_mem_nil, or_false] at hk'
      subst hk'
      unfold rangeClearOfRegion
      simp only [Bool.or_eq_true, decide_eq_true_eq, SeLe4n.MemoryRegion.endAddr,
        SeLe4n.PAddr.toNat, SeLe4n.PAddr.ofNat]
      right; omega
    · -- clear of every device the kernel drives
      intro d hd
      unfold rangeClearOfRegion
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      left
      have := hDev d hd
      omega
    · -- clear of every region map
      intro e' he'
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      obtain ⟨j, hj, hj'⟩ := List.mem_iff_getElem.mp he'
      subst hj'
      by_cases hjn : j = n
      · subst hjn; rw [hEn]; left; omega
      · have hR' : regionMapBaseOf (rpi5BootRamExtensions v)[j] ≥ (rpi5BootRamExtensions v)[j].1 := by
          unfold regionMapBaseOf; omega
        rcases hOther j hj hjn with h | h
        · right; omega
        · left; omega

theorem rpi5BoundPlatformConfigAt_rootServerMemoryPlaced (v : BCM2712Config) (hv : v.Admissible) :
    (rpi5BoundPlatformConfigAt v).rootServer.all
      (rootServerMemoryPlaced (rpi5BoundPlatformConfigAt v)) = true := by
  unfold rpi5BoundPlatformConfigAt
  cases h : rpi5RootServerAt v with
  | none => rfl
  | some rs =>
    unfold rpi5RootServerAt rootServerReservationOf at h
    cases hL : (rpi5BootRamExtensions v).getLast? with
    | none => rw [hL] at h; cases h
    | some e =>
      rw [hL, Option.map_some] at h
      have h' := Option.some.inj h
      exact rootServerMemoryPlaced_over v hv _ rfl rfl rfl rfl rs e hL
        (by rw [← h', paddr_toNat_ofNat]) (by rw [← h'])

/-- **WS-BP BP3.3, BP7.10**: the bound configuration is well-formed on every
    admissible configuration — the extent-free conjuncts because the
    member's are (`PlatformConfig.wellFormed_of_withoutExtents`), the untyped
    placement and (WS-SX SX5.1) the root server's pages over the structure. -/
theorem rpi5BoundPlatformConfigAt_wellFormed (v : BCM2712Config) (hv : v.Admissible) :
    (rpi5BoundPlatformConfigAt v).wellFormed = true :=
  PlatformConfig.wellFormed_of_withoutExtents _ _ (rpi5BoundPlatformConfigAt_withoutExtents v hv)
    (member_wellFormed _ hv.1) (rpi5BoundPlatformConfigAt_placement v hv)
    (rpi5BoundPlatformConfigAt_rootServerMemoryPlaced v hv)

/-- **WS-BP BP3.3**: every configured object passes the boot-safety sweep. -/
theorem rpi5BoundPlatformConfigAt_bootSafe (v : BCM2712Config) (hv : v.Admissible) :
    (rpi5BoundPlatformConfigAt v).initialObjects.all
      (fun entry => bootSafeObjectCheck entry.obj) = true := by
  rw [← bootSafe_withoutExtents, rpi5BoundPlatformConfigAt_withoutExtents v hv,
    bootSafe_withoutExtents]
  exact member_bootSafe _ hv.1

/-- **WS-BP BP3.3**: the three VSpace roots — the kernel's and the two threads'
    — are on three ASIDs. -/
theorem rpi5BoundPlatformConfigAt_asidsDistinct (v : BCM2712Config) (hv : v.Admissible) :
    bootVSpaceAsidsDistinct (rpi5BoundPlatformConfigAt v) = true := by
  rw [← bootVSpaceAsidsDistinct_withoutExtents, rpi5BoundPlatformConfigAt_withoutExtents v hv,
    bootVSpaceAsidsDistinct_withoutExtents]
  exact member_asidsDistinct _ hv.1

/-- **WS-BP BP3.3, BP7.10**: the bound machine configuration is well-formed —
    the family's own `rpi5Variants_wellFormed`, carried to the configuration's
    first-gigabyte top by `rpi5MachineConfigForVariant_wellFormed`. -/
theorem rpi5BoundPlatformConfigAt_machineConfig_wellFormed (v : BCM2712Config)
    (hv : v.Admissible) : (rpi5BoundPlatformConfigAt v).machineConfig.wellFormed = true :=
  rpi5MachineConfigForVariant_wellFormed v hv

/-- **WS-BP BP3.3**: the bound physical address width is the BCM2712's 40, on
    every configuration. -/
theorem rpi5BoundPlatformConfigAt_physicalAddressWidth (v : BCM2712Config) :
    (rpi5BoundPlatformConfigAt v).machineConfig.physicalAddressWidth ≤ 52 := by
  show (rpi5MachineConfigForVariant v).physicalAddressWidth ≤ 52
  rw [rpi5MachineConfigForVariant_physicalAddressWidth]
  decide

/-- **WS-BP BP3.3**: the binding's boot root collides with no configured
    object. -/
theorem rpi5BoundPlatformConfigAt_rootDistinct (v : BCM2712Config) (hv : v.Admissible) :
    bootVSpaceRootObjIdDistinct (rpi5BoundPlatformConfigAt v) = true := by
  rw [← bootVSpaceRootObjIdDistinct_withoutExtents, rpi5BoundPlatformConfigAt_withoutExtents v hv,
    bootVSpaceRootObjIdDistinct_withoutExtents]
  exact member_rootDistinct _ hv.1

/-- The bound configuration's boot root is the binding's, on every
    configuration. -/
theorem rpi5BoundPlatformConfigAt_bootVSpaceRoot (v : BCM2712Config) :
    (rpi5BoundPlatformConfigAt v).bootVSpaceRoot = some rpi5BootVSpaceRootEntry := rfl

/-- **WS-BP BP3.3**: the binding's boot root is not at the sentinel id. -/
theorem rpi5BoundPlatformConfigAt_rootNonSentinel (v : BCM2712Config) :
    bootVSpaceRootObjIdNonSentinel (rpi5BoundPlatformConfigAt v) = true := by
  unfold bootVSpaceRootObjIdNonSentinel
  rw [rpi5BoundPlatformConfigAt_bootVSpaceRoot]
  decide

/-- **WS-BP BP3.3**: the binding's boot root is boot-safe. -/
theorem rpi5BoundPlatformConfigAt_rootSafe (v : BCM2712Config) :
    bootVSpaceRootSafe (rpi5BoundPlatformConfigAt v) = true := by
  unfold bootVSpaceRootSafe
  rw [rpi5BoundPlatformConfigAt_bootVSpaceRoot]
  decide

/-- **WS-BP BP3.3**: every configured thread's affinity names a core the binding
    declares (both are unpinned). -/
theorem rpi5BoundPlatformConfigAt_affinities (v : BCM2712Config) (hv : v.Admissible) :
    bootAffinitiesDeclared (PlatformBinding.declaredCores (platform := RPi5Platform))
      (rpi5BoundPlatformConfigAt v) = true := by
  rw [← bootAffinitiesDeclared_withoutExtents, rpi5BoundPlatformConfigAt_withoutExtents v hv,
    bootAffinitiesDeclared_withoutExtents]
  exact member_affinities _ hv.1

/-- **WS-BP BP3.3**: the checked boot takes its success arm — the one with the
    binding's root installed — on every admissible configuration, so none of
    its nine refusals is reachable for this deployment on any Raspberry Pi 5
    whose firmware reports the kernel's extent as RAM. -/
theorem rpi5BoundPlatformConfigAt_checked (v : BCM2712Config) (hv : v.Admissible) :
    bootFromPlatformChecked (rpi5BoundPlatformConfigAt v) =
      .ok (bootEnableInterruptsOp
        (installBootVSpaceRoot (bootFromPlatform (rpi5BoundPlatformConfigAt v))
          rpi5BootVSpaceRootEntry.id rpi5BootVSpaceRootEntry.root
          rpi5BootVSpaceRootEntry.hMappings)) :=
  bootFromPlatformChecked_admits_bootVSpace _ (rpi5BoundPlatformConfigAt_wellFormed v hv)
    (rpi5BoundPlatformConfigAt_bootSafe v hv) (rpi5BoundPlatformConfigAt_asidsDistinct v hv)
    (rpi5BoundPlatformConfigAt_machineConfig_wellFormed v hv)
    (rpi5BoundPlatformConfigAt_physicalAddressWidth v)
    (rpi5BoundPlatformConfigAt_rootDistinct v hv)
    (rpi5BoundPlatformConfigAt_rootNonSentinel v)
    (rpi5BoundPlatformConfigAt_rootSafe v) rpi5BootVSpaceRootEntry rfl

-- ============================================================================
-- WS-BP BP3.4 / acceptance — the deployment boots, with both witnesses, on
-- every board account
-- ============================================================================

/-- **WS-BP BP7.11**: the idle stage of this deployment's boot on variant `v` —
    the checked boot with each declared core's idle thread stored, every
    configured thread still `.Inactive`.  (It was `rpi5DeploymentBootStateAt`
    until BP7.11, which added the stage that starts the initial threads.) -/
def rpi5DeploymentIdleStateAt (v : BCM2712Config) : IntermediateState :=
  (PlatformBinding.declaredCores (platform := RPi5Platform)).foldl storeIdleThread
    (bootEnableInterruptsOp
      (installBootVSpaceRoot (bootFromPlatform (rpi5BoundPlatformConfigAt v))
        rpi5BootVSpaceRootEntry.id rpi5BootVSpaceRootEntry.root
        rpi5BootVSpaceRootEntry.hMappings))

/-- **WS-BP BP7.11**: the started stage on variant `v`: the idle stage with both
    initial threads started. -/
def rpi5DeploymentStartedStateAt (v : BCM2712Config) : IntermediateState :=
  (PlatformBinding.initialThreads (platform := RPi5Platform)).foldl startInitialThread
    (rpi5DeploymentIdleStateAt v)

/-- The state the hardware boot installs for this deployment on variant `v`:
    the idle stage with **both initial threads started** (WS-BP BP7.11) — the
    root task on the boot core and the untrusted thread on
    `rpi5UntrustedCore`, the binding's `PlatformBinding.initialThreads`, which
    are its labeling's two separation witnesses — with the configuration's
    capabilities then linked into the derivation tree (WS-ZA ZA5.4,
    `linkBootCapabilities`), after the board's interrupt nodes are installed
    (WS-ZA ZA6.32, `installIrqNodes`) and the root task's IPC buffer built
    (WS-SX SX5.3, `installRootServer`). -/
def rpi5DeploymentBootStateAt (v : BCM2712Config) : IntermediateState :=
  linkBootCapabilities (rpi5BoundPlatformConfigAt v)
    (installRootServer (rpi5BoundPlatformConfigAt v)
      (installIrqNodes (irqNodeLineCount (rpi5BoundPlatformConfigAt v)) (rpi5DeploymentStartedStateAt v)))

/-- **WS-BP BP3.3**: the idle-thread boot on the binding's cores succeeds on
    every variant, and this is what it returns. -/
theorem rpi5BoundPlatformConfigAt_idleBoot (v : BCM2712Config) (hv : v.Admissible) :
    bootFromPlatformCheckedWithIdleThreadsFor
        (PlatformBinding.declaredCores (platform := RPi5Platform))
        (rpi5BoundPlatformConfigAt v) =
      .ok (rpi5DeploymentIdleStateAt v) :=
  bootFromPlatformCheckedWithIdleThreadsFor_map_ok _ _ _ (rpi5BoundPlatformConfigAt_checked v hv)
    (rpi5BoundPlatformConfigAt_affinities v hv) PlatformBinding.declaredCores_nodup

/-- ...and in its all-cores spelling, which the idle boot's characterisations
    are stated in — the RPi5 binding declares every model core. -/
private theorem rpi5BoundPlatformConfigAt_idleBoot_allCores (v : BCM2712Config)
    (hv : v.Admissible) :
    bootFromPlatformCheckedWithIdleThreads (rpi5BoundPlatformConfigAt v) =
      .ok (rpi5DeploymentIdleStateAt v) := by
  rw [← bootFromPlatformCheckedWithIdleThreadsFor_allCores, ← rpi5_cores_eq_allCores]
  exact rpi5BoundPlatformConfigAt_idleBoot v hv

/-- **WS-BP BP3.4**: a configured thread is a thread of the idle stage. -/
private theorem rpi5Deployment_tcb_idle (v : BCM2712Config) (hv : v.Admissible)
    (id : SeLe4n.ObjId) (tcb : TCB) (hMem : tcbEntry id tcb ∈ rpi5InitialObjectsFor v) :
    (rpi5DeploymentIdleStateAt v).state.getTcb? ⟨id.val⟩ = some tcb := by
  have h := bootFromPlatformCheckedWithIdleThreadsFor_ok_objects_of_mem _ _ _
    (rpi5BoundPlatformConfigAt_idleBoot v hv) _ hMem
  exact (SystemState.getTcb?_eq_some_iff _ _ _).mpr h

/-- **WS-BP BP7.11**: the binding's initial threads are the root task and the
    untrusted thread, in that order — its labeling's lower and upper witness. -/
theorem rpi5_initialThreads :
    PlatformBinding.initialThreads (platform := RPi5Platform) =
      [⟨rpi5RootTaskTcbId.val⟩, ⟨rpi5UntrustedTcbId.val⟩] := rfl

/-- **WS-BP BP7.11**: the bound configuration starts the binding's initial
    threads (it is `bindPlatformConfig`'s, by `rfl`). -/
theorem rpi5BoundPlatformConfigAt_initialThreads (v : BCM2712Config) :
    (rpi5BoundPlatformConfigAt v).initialThreads =
      PlatformBinding.initialThreads (platform := RPi5Platform) := rfl

/-- **WS-BP BP7.11**: neither initial thread is an idle thread. -/
private theorem rpi5_initialThreads_not_idle :
    (∀ c, (⟨rpi5RootTaskTcbId.val⟩ : SeLe4n.ThreadId) ≠ Kernel.idleThreadId c) ∧
    (∀ c, (⟨rpi5UntrustedTcbId.val⟩ : SeLe4n.ThreadId) ≠ Kernel.idleThreadId c) := by
  decide

/-- **WS-BP BP7.11**: the root task is startable on the idle stage. -/
private theorem rpi5Deployment_rootTask_startable (v : BCM2712Config) (hv : v.Admissible) :
    Kernel.initialThreadStartable (rpi5DeploymentIdleStateAt v).state
      ⟨rpi5RootTaskTcbId.val⟩ = true := by
  have hT := rpi5Deployment_tcb_idle v hv rpi5RootTaskTcbId
    (rpi5InitialThread rpi5RootTaskTcbId rpi5RootTaskCNodeId rpi5RootTaskVSpaceId)
    (by simp [rpi5InitialObjectsFor])
  exact bootFromPlatformCheckedWithIdleThreads_initialThreadStartable _ _
    (rpi5BoundPlatformConfigAt_idleBoot_allCores v hv) _ _ hT
    rpi5_initialThreads_not_idle.1 (by decide) rfl

/-- **WS-BP BP7.11**: the untrusted thread is startable on the idle stage. -/
private theorem rpi5Deployment_untrusted_startable (v : BCM2712Config) (hv : v.Admissible) :
    Kernel.initialThreadStartable (rpi5DeploymentIdleStateAt v).state
      ⟨rpi5UntrustedTcbId.val⟩ = true := by
  have hT := rpi5Deployment_tcb_idle v hv rpi5UntrustedTcbId rpi5UntrustedThread
    (by simp [rpi5InitialObjectsFor])
  exact bootFromPlatformCheckedWithIdleThreads_initialThreadStartable _ _
    (rpi5BoundPlatformConfigAt_idleBoot_allCores v hv) _ _ hT
    rpi5_initialThreads_not_idle.2 (by decide) rfl

/-- **WS-BP BP7.11**: both are startable on the idle stage — configured,
    `.Inactive`, unqueued, with the default time slice and no boost. -/
private theorem rpi5Deployment_initialThreads_startable (v : BCM2712Config)
    (hv : v.Admissible) :
    ∀ tid ∈ PlatformBinding.initialThreads (platform := RPi5Platform),
      Kernel.initialThreadStartable (rpi5DeploymentIdleStateAt v).state tid = true := by
  rw [rpi5_initialThreads]
  intro tid hMem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with h | h
  · rw [h]; exact rpi5Deployment_rootTask_startable v hv
  · rw [h]; exact rpi5Deployment_untrusted_startable v hv

/-- **WS-BP BP7.11**: the stage is the fold — neither start refused. -/
private theorem rpi5Deployment_startInitialThreads (v : BCM2712Config) (hv : v.Admissible) :
    startInitialThreads (PlatformBinding.initialThreads (platform := RPi5Platform))
        (rpi5DeploymentIdleStateAt v) = .ok (rpi5DeploymentStartedStateAt v) :=
  startInitialThreads_eq_foldl _ _ (by rw [rpi5_initialThreads]; decide)
    (rpi5Deployment_initialThreads_startable v hv)

/-- **WS-BP BP3.3, BP7.11**: the started boot on the binding's cores succeeds on
    every variant, and this is what it returns — neither start is refused. -/
theorem rpi5BoundPlatformConfigAt_boot (v : BCM2712Config) (hv : v.Admissible) :
    bootFromPlatformCheckedStartedFor
        (PlatformBinding.declaredCores (platform := RPi5Platform))
        (rpi5BoundPlatformConfigAt v) =
      .ok (rpi5DeploymentBootStateAt v) := by
  rw [bootFromPlatformCheckedStartedFor_of_idle _ _ _ (rpi5BoundPlatformConfigAt_idleBoot v hv),
    rpi5BoundPlatformConfigAt_initialThreads, rpi5Deployment_startInitialThreads v hv]
  rfl

/-- **WS-ZA ZA6.32**: the started state leaves every interrupt node's id free,
    on every variant. -/
theorem rpi5DeploymentStartedStateAt_irqNodesFresh (v : BCM2712Config) (hv : v.Admissible) :
    irqNodesFresh (irqNodeLineCount (rpi5BoundPlatformConfigAt v))
      (rpi5DeploymentStartedStateAt v).state = true :=
  bootFromPlatformCheckedStartedFor_irqNodesFresh _ _ _ _ (rpi5BoundPlatformConfigAt_idleBoot v hv)
    (by rw [rpi5BoundPlatformConfigAt_initialThreads]; exact rpi5Deployment_startInitialThreads v hv)

/-- **WS-BP BP3.4**: both threads the labeling declares separated are installed
    on the idle stage... -/
private theorem rpi5DeploymentIdleStateAt_witnessesInstalled (v : BCM2712Config)
    (hv : v.Admissible) :
    declaredWitnessesInstalled (rpi5DeploymentIdleStateAt v).state
      (PlatformBinding.labeling (platform := RPi5Platform)) = true := by
  unfold declaredWitnessesInstalled
  rw [rpi5_deploymentLabeling_separatedThreads]
  simp only [Bool.and_eq_true]
  have h1 := rpi5Deployment_tcb_idle v hv rpi5RootTaskTcbId
    (rpi5InitialThread rpi5RootTaskTcbId rpi5RootTaskCNodeId rpi5RootTaskVSpaceId)
    (by simp [rpi5InitialObjectsFor])
  have h2 := rpi5Deployment_tcb_idle v hv rpi5UntrustedTcbId rpi5UntrustedThread
    (by simp [rpi5InitialObjectsFor])
  exact ⟨Option.isSome_iff_exists.mpr ⟨_, h1⟩, Option.isSome_iff_exists.mpr ⟨_, h2⟩⟩

/-- **WS-BP BP3.4**: ...and on the started state the boot installs, so the boot's
    last refusal (`uninstalledSeparationWitnessBootError`) is unreachable too, on
    every variant. -/
theorem rpi5DeploymentBootStateAt_witnessesInstalled (v : BCM2712Config)
    (hv : v.Admissible) :
    declaredWitnessesInstalled (rpi5DeploymentBootStateAt v).state
      (PlatformBinding.labeling (platform := RPi5Platform)) = true :=
  (linkBootCapabilities_declaredWitnessesInstalled _ _ _).trans <|
  (installRootServer_declaredWitnessesInstalled _ _ _).trans <|
  (installIrqNodes_declaredWitnessesInstalled (rpi5DeploymentStartedStateAt_irqNodesFresh v hv) _).trans <|
  startInitialThreads_preserves_declaredWitnessesInstalled _ _ _
    (rpi5Deployment_startInitialThreads v hv) _
    (rpi5DeploymentIdleStateAt_witnessesInstalled v hv)

/-- Every configured object is notification-inert: the deployment queues no
    thread on its notification and binds none to it. -/
private theorem rpi5InitialObjectsFor_notificationInert (v : BCM2712Config) :
    ∀ e ∈ rpi5InitialObjectsFor v, notificationInertObject e.obj = true := by
  intro e he
  simp only [rpi5InitialObjectsFor, List.mem_cons, List.mem_append, List.mem_map,
    List.not_mem_nil, or_false] at he
  rcases he with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨u, -, rfl⟩ <;> rfl

/-- **The state the hardware boot installs is notification-label coherent**, on
    every variant and under every labeling, so the boot's coherence refusal
    (`incoherentNotificationLabelsBootError`) is unreachable for this
    deployment. -/
theorem rpi5DeploymentBootStateAt_notificationLabelsCoherent (v : BCM2712Config)
    (ctx : SeLe4n.Kernel.LabelingContext) :
    SeLe4n.Kernel.notificationLabelsCoherent (rpi5DeploymentBootStateAt v).state ctx = true :=
  notificationLabelsCoherent_of_inertObjects
    (rpi5DeploymentBootStateAt v).hAllTables.objects.1
    (bootPipeline_notificationInertObjects _ _ _ _ _ _ _
      (rpi5InitialObjectsFor_notificationInert v)) ctx

/-- **WS-BP BP7.11 — the payoff**: on the state the hardware boot installs,
    **both initial threads are started** — queued and stored `.Ready` — the root
    task in the boot domain and the untrusted thread in the other, so the
    labeling's two separation witnesses are threads that run.  Before BP7.11
    neither ever did, and the separation the labeling guard is decided on
    separated two threads that could never originate or receive a flow. -/
theorem rpi5DeploymentBootStateAt_initialThreadsStarted (v : BCM2712Config)
    (hv : v.Admissible) :
    Kernel.threadStarted (rpi5DeploymentBootStateAt v).state ⟨rpi5RootTaskTcbId.val⟩ ∧
    Kernel.threadStarted (rpi5DeploymentBootStateAt v).state ⟨rpi5UntrustedTcbId.val⟩ := by
  have h := bootFromPlatformCheckedStartedFor_started _ _ _ (rpi5BoundPlatformConfigAt_boot v hv)
  have hT : (rpi5BoundPlatformConfigAt v).initialThreads =
      [⟨rpi5RootTaskTcbId.val⟩, ⟨rpi5UntrustedTcbId.val⟩] := rpi5_initialThreads
  rw [hT] at h
  exact ⟨h _ (List.mem_cons_self ..), h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩

/-- **WS-BP BP3 acceptance, BP4.4 generalisation**: the hardware boot, given
    this deployment on **any** board account, commits the boot state of the
    variant that account selects and the binding's labeling, and returns `.ok`
    — every refusal arm is unreachable (`rpi5BoundPlatformConfigAt_checked`,
    `rpi5BoundPlatformConfigAt_affinities`,
    `rpi5DeploymentBootStateAt_witnessesInstalled`, and the labeling guard,
    which `PlatformBinding.labeling_admitted` discharges for every binding).
    The account is arbitrary because `rpi5VariantFor` always names an admissible
    configuration (`rpi5VariantFor_admissible`). -/
theorem bootAndInitialiseRPi5_rpi5PlatformConfigFor (board : SeLe4n.MachineConfig) :
    bootAndInitialiseRPi5 (rpi5PlatformConfigFor board) =
      (do
        completePhysicalWrites (rpi5DeploymentBootStateAt (rpi5VariantFor board)).state.drainedPhysicalWrites
        initialiseKernelState (drainBootPhysicalWrites (rpi5DeploymentBootStateAt (rpi5VariantFor board))).state
        initialiseKernelLabelingContext (PlatformBinding.labeling (platform := RPi5Platform))
        pure (Except.ok
          (drainBootPhysicalWrites (rpi5DeploymentBootStateAt (rpi5VariantFor board))).state)) := by
  have hv := rpi5VariantFor_admissible board
  rw [bootAndInitialiseRPi5_eq, bootAndInitialisePlatform_eq_checked_boot]
  show (match bootFromPlatformCheckedStartedFor _
      (bindPlatformConfig RPi5Platform (rpi5PlatformConfigFor board)) with
    | .error e => _ | .ok ist => _) = _
  rw [bindPlatformConfig_rpi5PlatformConfigFor, rpi5BoundPlatformConfigAt_boot _ hv]
  simp only [rpi5DeploymentBootStateAt_witnessesInstalled _ hv,
    rpi5DeploymentBootStateAt_notificationLabelsCoherent, ↓reduceIte]

/-- **WS-BP BP3 acceptance**: ...so the halting boot the entry reaches
    (`bootAndInitialiseRPi5OrHalt`) installs the deployment and never reaches
    `ffiFatalHaltAll` on it, whatever board account it is given. -/
theorem bootAndInitialiseRPi5OrHalt_rpi5PlatformConfigFor (board : SeLe4n.MachineConfig) :
    bootAndInitialiseRPi5OrHalt (rpi5PlatformConfigFor board) =
      (do
        completePhysicalWrites (rpi5DeploymentBootStateAt (rpi5VariantFor board)).state.drainedPhysicalWrites
        initialiseKernelState (drainBootPhysicalWrites (rpi5DeploymentBootStateAt (rpi5VariantFor board))).state
        initialiseKernelLabelingContext (PlatformBinding.labeling (platform := RPi5Platform))) := by
  exact bootAndInitialiseRPi5OrHalt_of_ok (bootAndInitialiseRPi5_rpi5PlatformConfigFor board)

/-- **WS-BP BP3.5**: the state the hardware boot installs for this deployment
    satisfies the proof-layer invariant bundle, and its freeze the frozen one —
    `bootToRuntime_invariantBridge_installed` at the binding's declared cores — on
    every variant.  Stated of the state `bootAndInitialiseRPi5OrHalt` installs,
    its physical-write ledger drained (WS-SX SX5.3, D15)
    (`bootAndInitialiseRPi5OrHalt_rpi5PlatformConfigFor`), not of a model of it. -/
theorem rpi5DeploymentBootStateAt_invariantBridge (v : BCM2712Config) (hv : v.Admissible) :
    SeLe4n.Kernel.Architecture.proofLayerInvariantBundle
      (drainBootPhysicalWrites (rpi5DeploymentBootStateAt v)).state ∧
    SeLe4n.Model.apiInvariantBundle_frozen
      (SeLe4n.Model.freeze (drainBootPhysicalWrites (rpi5DeploymentBootStateAt v))) :=
  bootToRuntime_invariantBridge_installed _ PlatformBinding.declaredCores_nodup _ _
    (rpi5BoundPlatformConfigAt_boot v hv)

-- ============================================================================
-- WS-BP BP4.4 — the configuration the device tree yields is this deployment's
-- ============================================================================

/-- **WS-BP BP4.4**: the device-tree bridge, given this deployment's caller half,
    yields exactly `rpi5PlatformConfigFor` of the board's own account — so every
    theorem above, stated over an arbitrary account, is a theorem about what the
    hardware entry boots. -/
theorem rpi5PlatformConfigFromDtb_deployment_ok (blob : ByteArray) (config : PlatformConfig)
    (h : rpi5PlatformConfigFromDtb blob rpi5InitialObjectsFor none = .ok config) :
    config = rpi5PlatformConfigFor config.machineConfig := by
  obtain ⟨dt, -, rfl⟩ := rpi5PlatformConfigFromDtb_ok_eq_fromDeviceTree _ _ _ _ h
  rfl

-- ============================================================================
-- WS-BP BP4.7 — the RAM the boot maps is the RAM the root task owns
-- ============================================================================

/-- **WS-BP BP4.7 (the payoff), re-derived at BP7.10**: every address a board's
    configuration declares RAM, outside the kernel's reserved extent, lies in
    some untyped the deployment hands the root task — one per extension
    (`bootRamExtensionsOf_covers`, read through `rpi5RootTaskUntypeds`).  So no
    RAM the boot maps is left idle, on any board: the direction the placement
    conjunct cannot state because it bounds the untypeds from above only.  With
    BP7.10 the extensions reach down to the kernel's extent, so the first
    gigabyte needs no case of its own — and only the part of it the firmware
    reported is in the map to be covered.  **WS-UC UC5**: except the region
    map's reservation at the top of each extension (`regionMapBaseOf`), which
    is the kernel's, as seL4's boot-time structures are, and (**WS-SX SX5.1**)
    the root server's pages below the last one (`rpi5RootServerAt`), which the
    boot builds the root task's IPC buffer from, as seL4's rootserver region is
    cut before any untyped is made. -/
theorem rpi5InitialObjectsFor_covers_ram (v : BCM2712Config)
    (r : SeLe4n.MemoryRegion) (hr : r ∈ rpi5MemoryMapForConfig v) (hk : r.kind = .ram)
    (a : Nat) (hlo : r.base.toNat ≤ a) (hhi : a < r.endAddr)
    (hk' : rpi5KernelReservedEnd ≤ a)
    (hMap : ∀ e ∈ rpi5BootRamExtensions v, e.1 ≤ a → a < regionMapBaseOf e)
    (hRoot : ∀ rs ∈ rpi5RootServerAt v,
      ¬ (rs.base.toNat ≤ a ∧ a < rs.base.toNat + rootServerReserveBytes)) :
    ∃ e ∈ rpi5InitialObjectsFor v, ∃ ut, e.obj = .untyped ut ∧ ut.isDevice = false ∧
      ut.regionBase.toNat ≤ a ∧ a < ut.regionBase.toNat + ut.regionSize := by
  obtain ⟨ext, hExt, h1, h2⟩ := bootRamExtensionsOf_covers _ r hr hk a hlo hhi hk'
  change ext ∈ rpi5BootRamExtensions v at hExt
  have hBelow := hMap ext hExt h1
  obtain ⟨i, hi, hEq⟩ := List.mem_iff_getElem.mp hExt
  have hi' : i < (untypedExtentsOf (rpi5BootRamExtensions v)).length := by simpa using hi
  refine ⟨untypedEntry (rpi5RootTaskUntypedId i)
      (rpi5InitialUntyped (untypedExtentsOf (rpi5BootRamExtensions v))[i].1
        (untypedExtentsOf (rpi5BootRamExtensions v))[i].2), ?_, _, rfl, rfl, ?_, ?_⟩
  · refine List.mem_append_right _ (List.mem_map.mpr ⟨(rpi5RootTaskUntypedId i,
      rpi5InitialUntyped (untypedExtentsOf (rpi5BootRamExtensions v))[i].1
        (untypedExtentsOf (rpi5BootRamExtensions v))[i].2), ?_, rfl⟩)
    unfold rpi5RootTaskUntypeds
    exact List.mem_mapIdx.mpr ⟨i, hi', rfl⟩
  · rw [rpi5InitialUntyped_base, (untypedExtentsOf_getElem _ i hi').1, hEq]; omega
  · rw [rpi5InitialUntyped_base, rpi5InitialUntyped_size, untypedExtentsOf_getElem_eq _ i hi, hEq]
    split
    · rename_i hLast
      -- the last extension: its untyped stops below the root server's pages
      have hL : (rpi5BootRamExtensions v).getLast? = some ext := by
        rw [List.getLast?_eq_getElem?, show (rpi5BootRamExtensions v).length - 1 = i by omega,
          List.getElem?_eq_getElem hi, hEq]
      have hRS : rpi5RootServerAt v = some
          { thread := ⟨rpi5LowerWitnessIndex⟩, base := SeLe4n.PAddr.ofNat (rootServerBaseOf ext),
            bufferVAddr := rpi5RootTaskIpcBufferVAddr, firstObjId := rpi5RootServerFirstObjId,
            frameSlot := SeLe4n.Slot.ofNat rpi5RootServerFrameSlot,
            ramExtensions := rpi5BootRamExtensions v } := by
        unfold rpi5RootServerAt rootServerReservationOf
        rw [hL, Option.map_some]
      have hNot := hRoot _ (by rw [hRS]; exact rfl)
      rw [paddr_toNat_ofNat] at hNot
      unfold untypedExtentBelowRootServerOf rootServerBaseOf at *
      unfold regionMapBaseOf at hBelow hNot
      simp only at hNot ⊢
      omega
    · unfold untypedExtentOf
      unfold regionMapBaseOf at hBelow
      simp only
      omega

/-- An untyped over the `i`-th of pairwise-disjoint extensions ends at or
    before the `j`-th extension's reservation, or the `j`-th extension ends at
    or before it begins.  Stated over the list with the sizes generalised, so
    the kernel never unfolds `untypedSizeOf`'s division. -/
private theorem untyped_clear_of_reservation (l : List (Nat × Nat))
    (hP : l.Pairwise (fun a b => a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1))
    (i j : Nat) (hi : i < l.length) (hj : j < l.length) (sz : Nat)
    (hsz : sz ≤ untypedSizeOf l[i].2) :
    l[i].1 + sz ≤ regionMapBaseOf l[j] ∨ l[j].1 + l[j].2 ≤ l[i].1 := by
  have hB : regionMapBaseOf l[j] = l[j].1 + untypedSizeOf l[j].2 := by
    unfold regionMapBaseOf; rfl
  rw [hB]
  by_cases hij : i = j
  · subst hij; exact Or.inl (by omega)
  · have hle := untypedSizeOf_le l[i].2
    have hP' := List.pairwise_iff_getElem.mp hP
    generalize untypedSizeOf l[i].2 = a at *
    generalize untypedSizeOf l[j].2 = b at *
    rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
    · rcases hP' i j hi hj hlt with h | h
      · left; omega
      · right; exact h
    · rcases hP' j i hj hi hgt with h | h
      · right; exact h
      · left; omega

/-- **WS-UC UC5**: no root-task untyped meets any extension's region-map
    reservation `[regionMapBaseOf e, e.1 + e.2)`, on every admissible
    configuration: an untyped ends where its own extension's reservation
    begins, and the extensions are pairwise disjoint.  So no capability the
    boot hands out names the map, and no carve can retype or map it. -/
theorem rpi5RootTaskUntypeds_clear_of_regionMaps (v : BCM2712Config) (hv : v.Admissible)
    (u : SeLe4n.ObjId × UntypedObject) (hu : u ∈ rpi5RootTaskUntypeds v)
    (e : Nat × Nat) (he : e ∈ rpi5BootRamExtensions v) :
    u.2.regionBase.toNat + u.2.regionSize ≤ regionMapBaseOf e ∨
      e.1 + e.2 ≤ u.2.regionBase.toNat := by
  unfold rpi5RootTaskUntypeds at hu
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hu
  obtain ⟨j, hj, hj'⟩ := List.mem_iff_getElem.mp he
  obtain ⟨hB, hS⟩ := untypedExtentsOf_getElem _ i hi
  have hi' : i < (rpi5BootRamExtensions v).length := by simpa using hi
  have h := untyped_clear_of_reservation _ (extensions_pairwise_disjoint v hv) i j hi' hj _ hS
  rw [hj', ← hB] at h
  show (rpi5InitialUntyped _ _).regionBase.toNat + (rpi5InitialUntyped _ _).regionSize ≤ _ ∨ _
  rw [rpi5InitialUntyped_base, rpi5InitialUntyped_size]
  exact h

/-- **WS-BP BP4.7**: and every one of those untypeds is an object of the state
    the hardware boot installs, at its own id, on every admissible
    configuration — so the RAM is not only described but handed over: the root
    task's CNode names each one (`rpi5RootTaskCNodeSlots`), and the boot
    installs it. -/
theorem rpi5DeploymentBootStateAt_untypedInstalled (v : BCM2712Config)
    (hv : v.Admissible) (u : SeLe4n.ObjId × UntypedObject)
    (hu : u ∈ rpi5RootTaskUntypeds v) :
    (rpi5DeploymentBootStateAt v).state.objects[u.1]? = some (.untyped u.2) :=
  ((linkBootCapabilities_agree _ _).obj_iff (fun _ e => by cases e)).mpr <|
  (fun h => installRootServer_objects_of_some h (fun _ e => by cases e) (fun _ e => by cases e)
    (fun _ e => by cases e)) <|
  installIrqNodes_objects_of_some (rpi5DeploymentStartedStateAt_irqNodesFresh v hv) <|
  startInitialThreads_objects_of_nonTcb _ _ _
    (rpi5Deployment_startInitialThreads v hv) _ _ (fun _ h => by cases h)
    (bootFromPlatformCheckedWithIdleThreadsFor_ok_objects_of_mem _ _ _
      (rpi5BoundPlatformConfigAt_idleBoot v hv) (untypedEntry u.1 u.2)
      (List.mem_append_right _ (List.mem_map.mpr ⟨u, hu, rfl⟩)))

/- **Tombstone (WS-BP BP7.10)**: `rpi5DeploymentBootStateAt_ramUntypedInstalled`
is `rpi5DeploymentBootStateAt_untypedInstalled` above, over every root-task
untyped rather than those above the gigabyte. -/

end SeLe4n.Platform.RPi5
