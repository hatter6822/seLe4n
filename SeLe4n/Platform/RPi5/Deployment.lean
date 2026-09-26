-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.FFI

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
| root task VSpace (ASID 1, empty) | `4` | boot |
| interrupt notification (every SPI signals it) | `5` | boot |
| untypeds over the board's RAM outside the kernel's extent, one per BP4.6 extension: the first gigabyte's `[256 MiB, lowRamTop)` as the firmware reports it, then — on every board larger than 1 GiB — the DRAM above the gigabyte (the BCM2712's DRAM is contiguous from 0) | `6`, … | boot |
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
* **Device interrupts go to the boot domain, SPIs only.**  The table registers
  every shared peripheral interrupt the contract supports (INTIDs 32–223,
  `rpi5InterruptContract`) to one notification, badged by INTID
  (`handleInterrupt`); SGIs are the kernel's inter-processor channel and PPIs are
  per-core (the timer PPI is the kernel's tick), so neither is delegated.
* **Both threads are `.Inactive`**, as `bootSafeTcbCheck` requires of every boot
  thread: the boot installs them and runs neither.  Starting the root task is the
  first thing the booted kernel does for userspace, and it is not a configuration
  fact.

## What is proved

`rpi5BoundPlatformConfigAt_wellFormed` and its siblings discharge every gate
of the checked boot **by evaluation** (BP3.3), on every member of the RAM family
(BP4.4) — `wellFormed` through the transparent duplicate checks
(`irqsUnique_eq_transparent`), every other gate by `decide`.
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
/-- The notification every delegated SPI signals. -/
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
    Its IPC buffer address is `0`: its address space maps nothing yet, and the
    thread maps a frame for its buffer out of its own memory before it can use
    one. -/
def rpi5InitialThread (id cspace vspace : SeLe4n.ObjId) : TCB :=
  { tid := ⟨id.val⟩
    priority := rpi5InitialThreadPriority
    domain := ⟨0⟩
    cspaceRoot := cspace
    vspaceRoot := vspace
    ipcBuffer := SeLe4n.VAddr.ofNat 0 }

/-- A capability to an object with the given rights, unbadged. -/
def rpi5InitialCap (target : SeLe4n.ObjId) (rights : List AccessRight) : Capability :=
  { target := .object target, rights := AccessRightSet.ofList rights }

/-- An initial CSpace: one level resolving a whole 64-bit CPtr — a 60-bit zero
    guard and 16 slots, seL4's root-CNode convention — so a capability address
    is its slot number.  Slot 0 is left empty. -/
def rpi5InitialCNode (slots : List (SeLe4n.Slot × Capability)) : CNode :=
  { depth := 64
    guardWidth := 60
    guardValue := 0
    radixWidth := 4
    slots := SeLe4n.UniqueSlotMap.ofListWF slots }

/-- An empty user address space on `asid` — what `bootSafeUserVSpaceRootCheck`
    admits. -/
def rpi5InitialVSpace (asid : SeLe4n.ASID) : VSpaceRoot :=
  { asid := asid, mappings := SeLe4n.Kernel.RobinHood.RHTable.empty 16 }

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
    gigabyte's part cut where the board's firmware said it ends. -/
def rpi5RootTaskUntypeds (v : BCM2712Config) : List (SeLe4n.ObjId × UntypedObject) :=
  (rpi5BootRamExtensions v).mapIdx fun i e =>
    (rpi5RootTaskUntypedId i, rpi5InitialUntyped e.1 e.2)

/-- **WS-BP BP4.7**: the untypeds' regions are exactly the extensions the boot
    maps, in order — on every configuration. -/
theorem rpi5RootTaskUntypeds_regions (v : BCM2712Config) :
    (rpi5RootTaskUntypeds v).map (fun u => (u.2.regionBase.toNat, u.2.regionSize)) =
      rpi5BootRamExtensions v := by
  apply List.ext_getElem
  · simp [rpi5RootTaskUntypeds]
  · intro i h₁ h₂
    simp [rpi5RootTaskUntypeds]

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
    `5 + i` (`rpi5RootTaskUntypedSlot`).  A function of the count, because a
    capability names an object and not its extent. -/
def rpi5RootTaskCNodeSlotsOfCount (n : Nat) : List (SeLe4n.Slot × Capability) :=
  [ (SeLe4n.Slot.ofNat 1, rpi5InitialCap rpi5RootTaskTcbId [.read, .write, .grant, .grantReply])
  , (SeLe4n.Slot.ofNat 2, rpi5InitialCap rpi5RootTaskCNodeId [.read, .write, .grant, .grantReply])
  , (SeLe4n.Slot.ofNat 3, rpi5InitialCap rpi5RootTaskVSpaceId [.read, .write])
  , (SeLe4n.Slot.ofNat 4, rpi5InitialCap rpi5InterruptNotificationId [.read, .write]) ] ++
  (List.range n).map fun i =>
    (rpi5RootTaskUntypedSlot i, rpi5InitialCap (rpi5RootTaskUntypedId i) [.read, .write, .retype])

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
    , (SeLe4n.Slot.ofNat 2, rpi5InitialCap rpi5UntrustedCNodeId [.read, .write, .grant, .grantReply])
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

private def vspaceEntry (id : SeLe4n.ObjId) (asid : SeLe4n.ASID) : ObjectEntry :=
  { id := id, obj := .vspaceRoot (rpi5InitialVSpace asid)
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
      { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none }
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
  , vspaceEntry rpi5RootTaskVSpaceId rpi5RootTaskAsid
  , notificationEntry rpi5InterruptNotificationId
  , tcbEntry rpi5UntrustedTcbId
      (rpi5InitialThread rpi5UntrustedTcbId rpi5UntrustedCNodeId rpi5UntrustedVSpaceId)
  , cnodeEntry rpi5UntrustedCNodeId rpi5UntrustedCNode
  , vspaceEntry rpi5UntrustedVSpaceId rpi5UntrustedAsid ] ++
  (rpi5RootTaskUntypeds v).map fun u => untypedEntry u.1 u.2

/-- **WS-BP BP3.1**: the IRQ table — every shared peripheral interrupt the
    interrupt contract supports (`rpi5InterruptContract.irqLineSupported`,
    INTIDs `32 … 32 + gicSpiCount - 1`) signals the boot domain's interrupt
    notification.  SGIs (0–15) and PPIs (16–31) are not delegated. -/
def rpi5IrqTable : List IrqEntry :=
  (List.range gicSpiCount).map fun i =>
    { irq := ⟨32 + i⟩, handler := rpi5InterruptNotificationId }

/-- **WS-BP BP3.1 / BP4.4**: the RPi5 deployment's configuration on a board
    account — the caller's half.  `bindPlatformConfig` supplies the binding's
    boot VSpace root and binds the machine configuration; `board` is only the
    *account* the binding selects a variant from.  The hardware entry takes it
    from the firmware's device tree (`PlatformConfig.fromDeviceTree`,
    `rpi5PlatformConfigFromDtb_ok_eq_fromDeviceTree`), so the deployment is
    stated over every account rather than over one board. -/
def rpi5PlatformConfigFor (board : SeLe4n.MachineConfig) : PlatformConfig :=
  { irqTable := rpi5IrqTable
    initialObjects := rpi5InitialObjectsFor (rpi5VariantFor board)
    machineConfig := board }

/-- **WS-BP BP4.4**: the configuration the hardware boot checks on a board whose
    account selects variant `v` — `bindPlatformConfig` at the RPi5 binding
    (`bindPlatformConfig_rpi5PlatformConfigFor`). -/
def rpi5BoundPlatformConfigAt (v : BCM2712Config) : PlatformConfig :=
  { irqTable := rpi5IrqTable
    initialObjects := rpi5InitialObjectsFor v
    machineConfig := rpi5MachineConfigForVariant v
    bootVSpaceRoot := PlatformBinding.bootVSpaceRoot (platform := RPi5Platform) }

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
    well-formed — all seven conjuncts.  The two duplicate checks run a hash set
    the kernel cannot reduce, so they are rewritten to their transparent forms
    first (`irqsUnique_eq_transparent`, `objectIdsUnique_eq_transparent`);
    everything else is `decide`. -/
private theorem member_wellFormed :
    ∀ v ∈ rpi5Variants, (rpi5BoundPlatformConfigAt v).wellFormed = true := by
  apply rpi5Variants_cases <;>
    (unfold PlatformConfig.wellFormed
     rw [irqsUnique_eq_transparent, objectIdsUnique_eq_transparent]
     decide)

private theorem member_bootSafe :
    ∀ v ∈ rpi5Variants, (rpi5BoundPlatformConfigAt v).initialObjects.all
      (fun entry => bootSafeObjectCheck entry.obj) = true := by
  apply rpi5Variants_cases <;> decide

private theorem member_asidsDistinct :
    ∀ v ∈ rpi5Variants, bootVSpaceAsidsDistinct (rpi5BoundPlatformConfigAt v) = true := by
  apply rpi5Variants_cases <;> decide

private theorem member_irqHandlers :
    ∀ v ∈ rpi5Variants, irqHandlersReferenceNotifications (rpi5BoundPlatformConfigAt v) = true := by
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
  unfold PlatformConfig.withoutExtents rpi5BoundPlatformConfigAt rpi5InitialObjectsFor
  simp only [List.map_append, hUnt, hSlots]
  rfl

/-- **WS-BP BP7.10**: an entry of the deployment that is an untyped is the
    `i`-th root-task untyped, over the `i`-th extension — none of the fixed
    seven objects is an untyped. -/
private theorem untyped_of_mem (v : BCM2712Config) (e : ObjectEntry) (ut : UntypedObject)
    (he : e ∈ rpi5InitialObjectsFor v) (hObj : e.obj = .untyped ut) :
    ∃ (i : Nat) (h : i < (rpi5BootRamExtensions v).length),
      e.id = rpi5RootTaskUntypedId i ∧
        ut = rpi5InitialUntyped (rpi5BootRamExtensions v)[i].1 (rpi5BootRamExtensions v)[i].2 := by
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
        obtain ⟨r, hr, hk, hlo, hend, hkre, _⟩ :=
          mem_bootRamExtensionsOf _ _ (List.getElem_mem hi)
        simp only [Bool.and_eq_true]
        refine ⟨?_, ?_⟩
        · unfold untypedWithinDeclaredRegion
          refine List.any_eq_true.mpr ⟨r, hr, ?_⟩
          simp only [untypedRegionKind, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
            rpi5InitialUntyped_base, rpi5InitialUntyped_size]
          refine ⟨⟨?_, hlo⟩, by omega⟩
          simp [rpi5InitialUntyped, hk]
        · unfold untypedClearOfKernel
          simp only [rpi5BoundPlatformConfigAt, rpi5MachineConfigForVariant_kernelReserved,
            rpi5KernelReserved, List.all_cons, List.all_nil, Bool.and_true, Bool.or_eq_true,
            decide_eq_true_eq, rpi5InitialUntyped_base, rpi5InitialUntyped_size]
          right
          simpa [SeLe4n.MemoryRegion.endAddr, SeLe4n.PAddr.ofNat, SeLe4n.PAddr.toNat] using hkre
    | _ => rfl
  · intro e₁ he₁ e₂ he₂
    unfold untypedEntriesDisjoint
    cases hO₁ : e₁.obj with
    | untyped u₁ =>
        cases hO₂ : e₂.obj with
        | untyped u₂ =>
            obtain ⟨i, hi, hId₁, rfl⟩ := untyped_of_mem v e₁ u₁ he₁ hO₁
            obtain ⟨j, hj, hId₂, rfl⟩ := untyped_of_mem v e₂ u₂ he₂ hO₂
            simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
            by_cases hij : i = j
            · subst hij; exact Or.inl (Or.inl (hId₁.trans hId₂.symm))
            · have hP := List.pairwise_iff_getElem.mp (extensions_pairwise_disjoint v hv)
              simp only [rpi5InitialUntyped]
              rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
              · rcases hP i j hi hj hlt with h | h
                · exact Or.inl (Or.inr h)
                · exact Or.inr h
              · rcases hP j i hj hi hgt with h | h
                · exact Or.inr h
                · exact Or.inl (Or.inr h)
        | _ => rfl
    | _ => rfl

/-- **WS-BP BP3.3, BP7.10**: the bound configuration is well-formed on every
    admissible configuration — the six extent-free conjuncts because the
    member's are (`PlatformConfig.wellFormed_of_withoutExtents`), the untyped
    placement over the structure. -/
theorem rpi5BoundPlatformConfigAt_wellFormed (v : BCM2712Config) (hv : v.Admissible) :
    (rpi5BoundPlatformConfigAt v).wellFormed = true :=
  PlatformConfig.wellFormed_of_withoutExtents _ _ (rpi5BoundPlatformConfigAt_withoutExtents v hv)
    (member_wellFormed _ hv.1) (rpi5BoundPlatformConfigAt_placement v hv)

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

/-- **WS-BP BP3.3**: every IRQ's handler is a notification in the config. -/
theorem rpi5BoundPlatformConfigAt_irqHandlers (v : BCM2712Config) (hv : v.Admissible) :
    irqHandlersReferenceNotifications (rpi5BoundPlatformConfigAt v) = true := by
  rw [← irqHandlersReferenceNotifications_withoutExtents,
    rpi5BoundPlatformConfigAt_withoutExtents v hv, irqHandlersReferenceNotifications_withoutExtents]
  exact member_irqHandlers _ hv.1

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
    its ten refusals is reachable for this deployment on any Raspberry Pi 5
    whose firmware reports the kernel's extent as RAM. -/
theorem rpi5BoundPlatformConfigAt_checked (v : BCM2712Config) (hv : v.Admissible) :
    bootFromPlatformChecked (rpi5BoundPlatformConfigAt v) =
      .ok (bootEnableInterruptsOp
        (installBootVSpaceRoot (bootFromPlatform (rpi5BoundPlatformConfigAt v))
          rpi5BootVSpaceRootEntry.id rpi5BootVSpaceRootEntry.root
          rpi5BootVSpaceRootEntry.hMappings)) :=
  bootFromPlatformChecked_admits_bootVSpace _ (rpi5BoundPlatformConfigAt_wellFormed v hv)
    (rpi5BoundPlatformConfigAt_bootSafe v hv) (rpi5BoundPlatformConfigAt_asidsDistinct v hv)
    (rpi5BoundPlatformConfigAt_irqHandlers v hv)
    (rpi5BoundPlatformConfigAt_machineConfig_wellFormed v hv)
    (rpi5BoundPlatformConfigAt_physicalAddressWidth v)
    (rpi5BoundPlatformConfigAt_rootDistinct v hv)
    (rpi5BoundPlatformConfigAt_rootNonSentinel v)
    (rpi5BoundPlatformConfigAt_rootSafe v) rpi5BootVSpaceRootEntry rfl

-- ============================================================================
-- WS-BP BP3.4 / acceptance — the deployment boots, with both witnesses, on
-- every board account
-- ============================================================================

/-- The state the hardware boot installs for this deployment on variant `v`:
    the checked boot with each declared core's idle thread enqueued. -/
def rpi5DeploymentBootStateAt (v : BCM2712Config) : IntermediateState :=
  (PlatformBinding.declaredCores (platform := RPi5Platform)).foldl enqueueIdleThread
    (bootEnableInterruptsOp
      (installBootVSpaceRoot (bootFromPlatform (rpi5BoundPlatformConfigAt v))
        rpi5BootVSpaceRootEntry.id rpi5BootVSpaceRootEntry.root
        rpi5BootVSpaceRootEntry.hMappings))

/-- **WS-BP BP3.3**: the idle-thread boot on the binding's cores succeeds on
    every variant, and this is what it returns. -/
theorem rpi5BoundPlatformConfigAt_boot (v : BCM2712Config) (hv : v.Admissible) :
    bootFromPlatformCheckedWithIdleThreadsFor
        (PlatformBinding.declaredCores (platform := RPi5Platform))
        (rpi5BoundPlatformConfigAt v) =
      .ok (rpi5DeploymentBootStateAt v) :=
  bootFromPlatformCheckedWithIdleThreadsFor_map_ok _ _ _ (rpi5BoundPlatformConfigAt_checked v hv)
    (rpi5BoundPlatformConfigAt_affinities v hv)

/-- **WS-BP BP3.4**: a configured thread is a thread of the boot state. -/
private theorem rpi5Deployment_tcb_installed (v : BCM2712Config) (hv : v.Admissible)
    (id cspace vspace : SeLe4n.ObjId)
    (hMem : tcbEntry id (rpi5InitialThread id cspace vspace) ∈ rpi5InitialObjectsFor v) :
    ((rpi5DeploymentBootStateAt v).state.getTcb? ⟨id.val⟩).isSome = true := by
  have h := bootFromPlatformCheckedWithIdleThreadsFor_ok_objects_of_mem _ _ _
    (rpi5BoundPlatformConfigAt_boot v hv) _ hMem
  have hTcb : (rpi5DeploymentBootStateAt v).state.getTcb? ⟨id.val⟩ =
      some (rpi5InitialThread id cspace vspace) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr h
  rw [hTcb]; rfl

/-- **WS-BP BP3.4**: both threads the labeling declares separated are installed
    — the root task at the lower witness, the untrusted initial thread at the
    upper — so the boot's last refusal (`uninstalledSeparationWitnessBootError`)
    is unreachable too, on every variant. -/
theorem rpi5DeploymentBootStateAt_witnessesInstalled (v : BCM2712Config)
    (hv : v.Admissible) :
    declaredWitnessesInstalled (rpi5DeploymentBootStateAt v).state
      (PlatformBinding.labeling (platform := RPi5Platform)) = true := by
  unfold declaredWitnessesInstalled
  rw [rpi5_deploymentLabeling_separatedThreads]
  simp only [Bool.and_eq_true]
  exact ⟨rpi5Deployment_tcb_installed v hv rpi5RootTaskTcbId rpi5RootTaskCNodeId
      rpi5RootTaskVSpaceId (by simp [rpi5InitialObjectsFor]),
    rpi5Deployment_tcb_installed v hv rpi5UntrustedTcbId rpi5UntrustedCNodeId
      rpi5UntrustedVSpaceId (by simp [rpi5InitialObjectsFor])⟩

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
        initialiseKernelState (rpi5DeploymentBootStateAt (rpi5VariantFor board)).state
        initialiseKernelLabelingContext (PlatformBinding.labeling (platform := RPi5Platform))
        pure (Except.ok (rpi5DeploymentBootStateAt (rpi5VariantFor board)).state)) := by
  have hv := rpi5VariantFor_admissible board
  rw [bootAndInitialiseRPi5_eq, bootAndInitialisePlatform_eq_checked_boot]
  show (match bootFromPlatformCheckedWithIdleThreadsFor _
      (bindPlatformConfig RPi5Platform (rpi5PlatformConfigFor board)) with
    | .error e => _ | .ok ist => _) = _
  rw [bindPlatformConfig_rpi5PlatformConfigFor, rpi5BoundPlatformConfigAt_boot _ hv]
  simp only [rpi5DeploymentBootStateAt_witnessesInstalled _ hv, ↓reduceIte]

/-- **WS-BP BP3 acceptance**: ...so the halting boot the entry reaches
    (`bootAndInitialiseRPi5OrHalt`) installs the deployment and never reaches
    `ffiFatalHaltAll` on it, whatever board account it is given. -/
theorem bootAndInitialiseRPi5OrHalt_rpi5PlatformConfigFor (board : SeLe4n.MachineConfig) :
    bootAndInitialiseRPi5OrHalt (rpi5PlatformConfigFor board) =
      (do
        initialiseKernelState (rpi5DeploymentBootStateAt (rpi5VariantFor board)).state
        initialiseKernelLabelingContext (PlatformBinding.labeling (platform := RPi5Platform))) := by
  unfold bootAndInitialiseRPi5OrHalt
  rw [bootAndInitialiseRPi5_rpi5PlatformConfigFor]
  -- `BaseIO` carries no `LawfulMonad` instance to rewrite with, and needs
  -- none: its bind reduces, so the two programs are the same term.
  rfl

/-- **WS-BP BP3.5**: the state the hardware boot installs for this deployment
    satisfies the proof-layer invariant bundle, and its freeze the frozen one —
    `bootToRuntime_invariantBridge_checked` at the binding's declared cores — on
    every variant.  Stated of the state `bootAndInitialiseRPi5OrHalt` installs
    (`bootAndInitialiseRPi5OrHalt_rpi5PlatformConfigFor`), not of a model of it. -/
theorem rpi5DeploymentBootStateAt_invariantBridge (v : BCM2712Config) (hv : v.Admissible) :
    SeLe4n.Kernel.Architecture.proofLayerInvariantBundle (rpi5DeploymentBootStateAt v).state ∧
    SeLe4n.Model.apiInvariantBundle_frozen (SeLe4n.Model.freeze (rpi5DeploymentBootStateAt v)) :=
  bootToRuntime_invariantBridge_checked _ PlatformBinding.declaredCores_nodup _ _
    (rpi5BoundPlatformConfigAt_boot v hv)

-- ============================================================================
-- WS-BP BP4.4 — the configuration the device tree yields is this deployment's
-- ============================================================================

/-- **WS-BP BP4.4**: the device-tree bridge, given this deployment's caller half,
    yields exactly `rpi5PlatformConfigFor` of the board's own account — so every
    theorem above, stated over an arbitrary account, is a theorem about what the
    hardware entry boots. -/
theorem rpi5PlatformConfigFromDtb_deployment_ok (blob : ByteArray) (config : PlatformConfig)
    (h : rpi5PlatformConfigFromDtb blob rpi5IrqTable rpi5InitialObjectsFor none = .ok config) :
    config = rpi5PlatformConfigFor config.machineConfig := by
  obtain ⟨dt, -, rfl⟩ := rpi5PlatformConfigFromDtb_ok_eq_fromDeviceTree _ _ _ _ _ h
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
    reported is in the map to be covered. -/
theorem rpi5InitialObjectsFor_covers_ram (v : BCM2712Config)
    (r : SeLe4n.MemoryRegion) (hr : r ∈ rpi5MemoryMapForConfig v) (hk : r.kind = .ram)
    (a : Nat) (hlo : r.base.toNat ≤ a) (hhi : a < r.endAddr)
    (hk' : rpi5KernelReservedEnd ≤ a) :
    ∃ e ∈ rpi5InitialObjectsFor v, ∃ ut, e.obj = .untyped ut ∧ ut.isDevice = false ∧
      ut.regionBase.toNat ≤ a ∧ a < ut.regionBase.toNat + ut.regionSize := by
  obtain ⟨ext, hExt, h1, h2⟩ := bootRamExtensionsOf_covers _ r hr hk a hlo hhi hk'
  obtain ⟨i, hi, hEq⟩ := List.mem_iff_getElem.mp hExt
  refine ⟨untypedEntry (rpi5RootTaskUntypedId i) (rpi5InitialUntyped ext.1 ext.2), ?_,
    _, rfl, rfl, ?_, ?_⟩
  · refine List.mem_append_right _ (List.mem_map.mpr ⟨(rpi5RootTaskUntypedId i,
      rpi5InitialUntyped ext.1 ext.2), ?_, rfl⟩)
    unfold rpi5RootTaskUntypeds
    exact List.mem_mapIdx.mpr ⟨i, hi, by rw [← hEq]; rfl⟩
  · simp only [rpi5InitialUntyped_base]; omega
  · simp only [rpi5InitialUntyped_base, rpi5InitialUntyped_size]; omega

/-- **WS-BP BP4.7**: and every one of those untypeds is an object of the state
    the hardware boot installs, at its own id, on every admissible
    configuration — so the RAM is not only described but handed over: the root
    task's CNode names each one (`rpi5RootTaskCNodeSlots`), and the boot
    installs it. -/
theorem rpi5DeploymentBootStateAt_untypedInstalled (v : BCM2712Config)
    (hv : v.Admissible) (u : SeLe4n.ObjId × UntypedObject)
    (hu : u ∈ rpi5RootTaskUntypeds v) :
    (rpi5DeploymentBootStateAt v).state.objects[u.1]? = some (.untyped u.2) :=
  bootFromPlatformCheckedWithIdleThreadsFor_ok_objects_of_mem _ _ _
    (rpi5BoundPlatformConfigAt_boot v hv) (untypedEntry u.1 u.2)
    (List.mem_append_right _ (List.mem_map.mpr ⟨u, hu, rfl⟩))

/- **Tombstone (WS-BP BP7.10)**: `rpi5DeploymentBootStateAt_ramUntypedInstalled`
is `rpi5DeploymentBootStateAt_untypedInstalled` above, over every root-task
untyped rather than those above the gigabyte. -/

end SeLe4n.Platform.RPi5
