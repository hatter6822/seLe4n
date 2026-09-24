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
that configuration, `rpi5PlatformConfig`, and the proof that it boots.

## What it is

The caller's half of a `PlatformConfig` (BP3.1): the IRQ table and the initial
objects.  The other two fields — the machine configuration and the boot VSpace
root — are the binding's, supplied by `bindPlatformConfig`, so the machine
configuration here is only the *board account* the binding selects a variant
from (the smallest board, until the device-tree path supplies a real one).

Two domains, as `confinedDeploymentLabeling` declares them (BP3.4), each with one
initial thread, its CSpace and its own address space (BP3.2):

| Object | Id | Domain |
|---|---|---|
| root task TCB (the lower separation witness) | `2` | boot (`lowTrusted`) |
| root task CNode | `3` | boot |
| root task VSpace (ASID 1, empty) | `4` | boot |
| interrupt notification (every SPI signals it) | `5` | boot |
| untyped `[256 MiB, 512 MiB)` | `6` | boot |
| untyped `[512 MiB, 1 GiB)` | `7` | boot |
| untrusted initial TCB (the upper separation witness) | `0x10_0000` | untrusted (`highUntrusted`) |
| its CNode | `0x10_0001` | untrusted |
| its VSpace (ASID 2, empty) | `0x10_0002` | untrusted |

Four decisions, each a consequence of a rule elsewhere rather than a choice made
here:

* **The untypeds are the guaranteed gigabyte minus the kernel's reserved
  extent** — `[rpi5KernelReservedEnd, 1 GiB)`, split on power-of-two bounds.  The
  boot refuses anything else (`untypedPlacementRespected`), and RAM above the
  gigabyte is unmapped until BP4.6 extends the boot map, so it is not yet memory
  the kernel can hand out.  Only the boot domain holds untypeds: memory is
  authority, and the untrusted domain's share is the boot domain's to delegate.
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

`rpi5PlatformConfig_bound_wellFormed` and its siblings discharge every gate of
the checked boot **by evaluation** (BP3.3) — `wellFormed` through the
transparent duplicate checks (`irqsUnique_eq_transparent`), every other gate by
`decide`.  `rpi5PlatformConfig_boots` is the acceptance statement: the checked
boot on the binding's cores succeeds and installs both witness threads, so
`bootAndInitialiseRPi5 rpi5PlatformConfig` commits its state and labeling
(`bootAndInitialiseRPi5_rpi5PlatformConfig`) and the halting entry the boot seam
calls never halts on it (`bootAndInitialiseRPi5OrHalt_rpi5PlatformConfig`).
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
/-- The lower untyped, `[256 MiB, 512 MiB)`. -/
def rpi5RootTaskUntypedLowId : SeLe4n.ObjId := ⟨6⟩
/-- The upper untyped, `[512 MiB, 1 GiB)`. -/
def rpi5RootTaskUntypedHighId : SeLe4n.ObjId := ⟨7⟩
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

/-- The root task's CNode: its own TCB, CNode and VSpace, the interrupt
    notification, and the two untypeds. -/
def rpi5RootTaskCNode : CNode :=
  rpi5InitialCNode
    [ (SeLe4n.Slot.ofNat 1, rpi5InitialCap rpi5RootTaskTcbId [.read, .write, .grant, .grantReply])
    , (SeLe4n.Slot.ofNat 2, rpi5InitialCap rpi5RootTaskCNodeId [.read, .write, .grant, .grantReply])
    , (SeLe4n.Slot.ofNat 3, rpi5InitialCap rpi5RootTaskVSpaceId [.read, .write])
    , (SeLe4n.Slot.ofNat 4, rpi5InitialCap rpi5InterruptNotificationId [.read, .write])
    , (SeLe4n.Slot.ofNat 5, rpi5InitialCap rpi5RootTaskUntypedLowId [.read, .write, .retype])
    , (SeLe4n.Slot.ofNat 6, rpi5InitialCap rpi5RootTaskUntypedHighId [.read, .write, .retype]) ]

/-- The untrusted initial thread's CNode: its own TCB, CNode and VSpace, and
    nothing of the boot domain's. -/
def rpi5UntrustedCNode : CNode :=
  rpi5InitialCNode
    [ (SeLe4n.Slot.ofNat 1, rpi5InitialCap rpi5UntrustedTcbId [.read, .write, .grant, .grantReply])
    , (SeLe4n.Slot.ofNat 2, rpi5InitialCap rpi5UntrustedCNodeId [.read, .write, .grant, .grantReply])
    , (SeLe4n.Slot.ofNat 3, rpi5InitialCap rpi5UntrustedVSpaceId [.read, .write]) ]

/-- A normal-memory untyped over `[base, base + size)`, with nothing carved. -/
def rpi5InitialUntyped (base size : Nat) : UntypedObject :=
  { regionBase := SeLe4n.PAddr.ofNat base, regionSize := size }

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

private def notificationEntry (id : SeLe4n.ObjId) : ObjectEntry :=
  { id := id
    obj := .notification
      { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none }
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => nomatch h }

/-- **WS-BP BP3.2**: the initial objects. -/
def rpi5InitialObjects : List ObjectEntry :=
  [ tcbEntry rpi5RootTaskTcbId
      (rpi5InitialThread rpi5RootTaskTcbId rpi5RootTaskCNodeId rpi5RootTaskVSpaceId)
  , cnodeEntry rpi5RootTaskCNodeId rpi5RootTaskCNode
  , vspaceEntry rpi5RootTaskVSpaceId rpi5RootTaskAsid
  , notificationEntry rpi5InterruptNotificationId
  , untypedEntry rpi5RootTaskUntypedLowId (rpi5InitialUntyped 0x1000_0000 0x1000_0000)
  , untypedEntry rpi5RootTaskUntypedHighId (rpi5InitialUntyped 0x2000_0000 0x2000_0000)
  , tcbEntry rpi5UntrustedTcbId
      (rpi5InitialThread rpi5UntrustedTcbId rpi5UntrustedCNodeId rpi5UntrustedVSpaceId)
  , cnodeEntry rpi5UntrustedCNodeId rpi5UntrustedCNode
  , vspaceEntry rpi5UntrustedVSpaceId rpi5UntrustedAsid ]

/-- **WS-BP BP3.1**: the IRQ table — every shared peripheral interrupt the
    interrupt contract supports (`rpi5InterruptContract.irqLineSupported`,
    INTIDs `32 … 32 + gicSpiCount - 1`) signals the boot domain's interrupt
    notification.  SGIs (0–15) and PPIs (16–31) are not delegated. -/
def rpi5IrqTable : List IrqEntry :=
  (List.range gicSpiCount).map fun i =>
    { irq := ⟨32 + i⟩, handler := rpi5InterruptNotificationId }

/-- **WS-BP BP3.1**: the RPi5 deployment's configuration — the caller's half.
    `bindPlatformConfig` supplies the binding's boot VSpace root and binds the
    machine configuration; the one given here is the board account, the smallest
    board, which binds the smallest variant: the memory every Raspberry Pi 5
    has. -/
def rpi5PlatformConfig : PlatformConfig :=
  { irqTable := rpi5IrqTable
    initialObjects := rpi5InitialObjects
    machineConfig := rpi5MachineConfigForVariant rpi5SmallestVariant }

/-- The configuration the hardware boot actually checks. -/
abbrev rpi5BoundPlatformConfig : PlatformConfig :=
  bindPlatformConfig RPi5Platform rpi5PlatformConfig

-- ============================================================================
-- WS-BP BP3.3 — every gate of the checked boot, discharged by evaluation
-- ============================================================================

/-- **WS-BP BP3.3**: the bound configuration is well-formed — all seven
    conjuncts, `idleSlotsReserved`, `embeddedIdentitiesMatchSlots`,
    `declaredCoreCountInRange` and the untyped placement among them.  The two
    duplicate checks run a hash set the kernel cannot reduce, so they are
    rewritten to their transparent forms first (`irqsUnique_eq_transparent`,
    `objectIdsUnique_eq_transparent`); everything else is `decide`. -/
theorem rpi5BoundPlatformConfig_wellFormed : rpi5BoundPlatformConfig.wellFormed = true := by
  unfold PlatformConfig.wellFormed
  rw [irqsUnique_eq_transparent, objectIdsUnique_eq_transparent]
  decide

/-- **WS-BP BP3.3**: every configured object passes the boot-safety sweep. -/
theorem rpi5BoundPlatformConfig_bootSafe :
    rpi5BoundPlatformConfig.initialObjects.all (fun entry => bootSafeObjectCheck entry.obj) =
      true := by
  decide

/-- **WS-BP BP3.3**: the three VSpace roots — the kernel's and the two threads'
    — are on three ASIDs. -/
theorem rpi5BoundPlatformConfig_asidsDistinct :
    bootVSpaceAsidsDistinct rpi5BoundPlatformConfig = true := by
  decide

/-- **WS-BP BP3.3**: every IRQ's handler is a notification in the config. -/
theorem rpi5BoundPlatformConfig_irqHandlers :
    irqHandlersReferenceNotifications rpi5BoundPlatformConfig = true := by
  decide

/-- **WS-BP BP3.3**: the bound machine configuration is well-formed. -/
theorem rpi5BoundPlatformConfig_machineConfig_wellFormed :
    rpi5BoundPlatformConfig.machineConfig.wellFormed = true := by
  decide

/-- **WS-BP BP3.3**: the bound physical address width is the BCM2712's 44. -/
theorem rpi5BoundPlatformConfig_physicalAddressWidth :
    rpi5BoundPlatformConfig.machineConfig.physicalAddressWidth ≤ 52 := by
  decide

/-- **WS-BP BP3.3**: the binding's boot root collides with no configured
    object. -/
theorem rpi5BoundPlatformConfig_rootDistinct :
    bootVSpaceRootObjIdDistinct rpi5BoundPlatformConfig = true := by
  decide

/-- **WS-BP BP3.3**: the binding's boot root is not at the sentinel id. -/
theorem rpi5BoundPlatformConfig_rootNonSentinel :
    bootVSpaceRootObjIdNonSentinel rpi5BoundPlatformConfig = true := by
  decide

/-- **WS-BP BP3.3**: the binding's boot root is boot-safe. -/
theorem rpi5BoundPlatformConfig_rootSafe :
    bootVSpaceRootSafe rpi5BoundPlatformConfig = true := by
  decide

/-- **WS-BP BP3.3**: every configured thread's affinity names a core the binding
    declares (both are unpinned). -/
theorem rpi5BoundPlatformConfig_affinities :
    bootAffinitiesDeclared (PlatformBinding.declaredCores (platform := RPi5Platform))
      rpi5BoundPlatformConfig = true := by
  decide

/-- **WS-BP BP3.3**: the checked boot takes its success arm — the one with the
    binding's root installed — so none of its ten refusals is reachable for
    this configuration. -/
theorem rpi5BoundPlatformConfig_checked :
    bootFromPlatformChecked rpi5BoundPlatformConfig =
      .ok (bootEnableInterruptsOp
        (installBootVSpaceRoot (bootFromPlatform rpi5BoundPlatformConfig)
          rpi5BootVSpaceRootEntry.id rpi5BootVSpaceRootEntry.root
          rpi5BootVSpaceRootEntry.hMappings)) :=
  bootFromPlatformChecked_admits_bootVSpace _ rpi5BoundPlatformConfig_wellFormed
    rpi5BoundPlatformConfig_bootSafe rpi5BoundPlatformConfig_asidsDistinct
    rpi5BoundPlatformConfig_irqHandlers rpi5BoundPlatformConfig_machineConfig_wellFormed
    rpi5BoundPlatformConfig_physicalAddressWidth rpi5BoundPlatformConfig_rootDistinct
    rpi5BoundPlatformConfig_rootNonSentinel rpi5BoundPlatformConfig_rootSafe
    rpi5BootVSpaceRootEntry rfl

-- ============================================================================
-- WS-BP BP3.4 / acceptance — the deployment boots, with both witnesses
-- ============================================================================

/-- The state the hardware boot installs for this deployment: the checked boot
    with each declared core's idle thread enqueued. -/
def rpi5DeploymentBootState : IntermediateState :=
  (PlatformBinding.declaredCores (platform := RPi5Platform)).foldl enqueueIdleThread
    (bootEnableInterruptsOp
      (installBootVSpaceRoot (bootFromPlatform rpi5BoundPlatformConfig)
        rpi5BootVSpaceRootEntry.id rpi5BootVSpaceRootEntry.root
        rpi5BootVSpaceRootEntry.hMappings))

/-- **WS-BP BP3.3**: the idle-thread boot on the binding's cores succeeds, and
    this is what it returns. -/
theorem rpi5BoundPlatformConfig_boot :
    bootFromPlatformCheckedWithIdleThreadsFor
        (PlatformBinding.declaredCores (platform := RPi5Platform)) rpi5BoundPlatformConfig =
      .ok rpi5DeploymentBootState :=
  bootFromPlatformCheckedWithIdleThreadsFor_map_ok _ _ _ rpi5BoundPlatformConfig_checked
    rpi5BoundPlatformConfig_affinities

/-- **WS-BP BP3.4**: a configured thread is a thread of the boot state. -/
private theorem rpi5Deployment_tcb_installed (id cspace vspace : SeLe4n.ObjId)
    (hMem : tcbEntry id (rpi5InitialThread id cspace vspace) ∈
      rpi5BoundPlatformConfig.initialObjects) :
    (rpi5DeploymentBootState.state.getTcb? ⟨id.val⟩).isSome = true := by
  have h := bootFromPlatformCheckedWithIdleThreadsFor_ok_objects_of_mem _ _ _
    rpi5BoundPlatformConfig_boot _ hMem
  have hTcb : rpi5DeploymentBootState.state.getTcb? ⟨id.val⟩ =
      some (rpi5InitialThread id cspace vspace) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr h
  rw [hTcb]; rfl

/-- **WS-BP BP3.4**: both threads the labeling declares separated are installed
    — the root task at the lower witness, the untrusted initial thread at the
    upper — so the boot's last refusal (`uninstalledSeparationWitnessBootError`)
    is unreachable too. -/
theorem rpi5DeploymentBootState_witnessesInstalled :
    declaredWitnessesInstalled rpi5DeploymentBootState.state
      (PlatformBinding.labeling (platform := RPi5Platform)) = true := by
  unfold declaredWitnessesInstalled
  rw [rpi5_deploymentLabeling_separatedThreads]
  simp only [Bool.and_eq_true]
  exact ⟨rpi5Deployment_tcb_installed rpi5RootTaskTcbId rpi5RootTaskCNodeId
      rpi5RootTaskVSpaceId (by show _ ∈ rpi5InitialObjects; simp [rpi5InitialObjects]),
    rpi5Deployment_tcb_installed rpi5UntrustedTcbId rpi5UntrustedCNodeId
      rpi5UntrustedVSpaceId (by show _ ∈ rpi5InitialObjects; simp [rpi5InitialObjects])⟩

/-- **WS-BP BP3 acceptance**: the hardware boot entry, given this deployment,
    commits the boot state and the binding's labeling and returns `.ok` — every
    refusal arm is unreachable (`rpi5BoundPlatformConfig_checked`,
    `rpi5BoundPlatformConfig_affinities`,
    `rpi5DeploymentBootState_witnessesInstalled`, and the labeling guard, which
    `PlatformBinding.labeling_admitted` discharges for every binding). -/
theorem bootAndInitialiseRPi5_rpi5PlatformConfig :
    bootAndInitialiseRPi5 rpi5PlatformConfig =
      (do
        initialiseKernelState rpi5DeploymentBootState.state
        initialiseKernelLabelingContext (PlatformBinding.labeling (platform := RPi5Platform))
        pure (Except.ok rpi5DeploymentBootState.state)) := by
  rw [bootAndInitialiseRPi5_eq, bootAndInitialisePlatform_eq_checked_boot]
  show (match bootFromPlatformCheckedWithIdleThreadsFor _ rpi5BoundPlatformConfig with
    | .error e => _ | .ok ist => _) = _
  rw [rpi5BoundPlatformConfig_boot]
  simp only [rpi5DeploymentBootState_witnessesInstalled, ↓reduceIte]

/-- **WS-BP BP3 acceptance**: ...so the halting entry the boot seam calls
    (`bootAndInitialiseRPi5OrHalt`) installs the deployment and never reaches
    `ffiFatalHaltAll` on it. -/
theorem bootAndInitialiseRPi5OrHalt_rpi5PlatformConfig :
    bootAndInitialiseRPi5OrHalt rpi5PlatformConfig =
      (do
        initialiseKernelState rpi5DeploymentBootState.state
        initialiseKernelLabelingContext (PlatformBinding.labeling (platform := RPi5Platform))) := by
  unfold bootAndInitialiseRPi5OrHalt
  rw [bootAndInitialiseRPi5_rpi5PlatformConfig]
  -- `BaseIO` carries no `LawfulMonad` instance to rewrite with, and needs
  -- none: its bind reduces, so the two programs are the same term.
  rfl

end SeLe4n.Platform.RPi5
