-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.QemuVirt.BootEntry
import SeLe4n.Platform.RPi5.Deployment

/-!
# QEMU `virt` — the deployment the `virt` boot installs (WS-BP BP8.1)

The Raspberry Pi 5 deployment's object layout (`RPi5/Deployment.lean`), on this
board's RAM and table pool: two domains as the confined labeling declares them,
each with one initial thread, its CSpace and its own empty address space, and
the root task holding one untyped over all the RAM outside the kernel's extent.

| Object | Id | Domain |
|---|---|---|
| root task TCB (the lower separation witness) | `2` | boot |
| root task CNode | `3` | boot |
| root task VSpace (ASID 1, pool page 0) | `4` | boot |
| interrupt notification (every SPI signals it) | `5` | boot |
| untyped over `[0x5000_0000, 0x8000_0000)` | `6` | boot |
| untrusted initial TCB (the upper witness, pinned to core 1) | `0x10_0000` | untrusted |
| its CNode | `0x10_0001` | untrusted |
| its VSpace (ASID 2, pool page 1) | `0x10_0002` | untrusted |

The object *builders* are the RPi5 deployment's (`rpi5InitialThread`,
`rpi5InitialCap`, `rpi5InitialCNode`, `rpi5InitialUntyped`), which read no
board constant; only what names this board — the table pool, the untyped's
extent, the SPI count — is this module's.

Because `virt` is one fixed configuration, every gate of the checked boot is
decided outright (`qemuVirtBoundPlatformConfig_*`), and the boot is proved to
accept this deployment and install both witnesses on every board account
(`bootAndInitialiseQemuVirt_qemuVirtPlatformConfigFor`).
-/

namespace SeLe4n.Platform.QemuVirt

open SeLe4n.Model
open SeLe4n.Platform.Boot
open SeLe4n.Platform.FFI
open SeLe4n.Platform.RPi5 (rpi5InitialThread rpi5InitialCap rpi5InitialCNode rpi5InitialUntyped)

/-- The root task's TCB — the lower separation witness. -/
def qemuVirtRootTaskTcbId : SeLe4n.ObjId := ⟨qemuVirtLowerWitnessIndex⟩
/-- The root task's CNode. -/
def qemuVirtRootTaskCNodeId : SeLe4n.ObjId := ⟨3⟩
/-- The root task's VSpace. -/
def qemuVirtRootTaskVSpaceId : SeLe4n.ObjId := ⟨4⟩
/-- The notification every delegated SPI signals. -/
def qemuVirtInterruptNotificationId : SeLe4n.ObjId := ⟨5⟩
/-- The root task's untyped over the RAM outside the kernel's extent. -/
def qemuVirtRootTaskUntypedId : SeLe4n.ObjId := ⟨6⟩
/-- The untrusted domain's initial TCB — the upper separation witness. -/
def qemuVirtUntrustedTcbId : SeLe4n.ObjId := ⟨qemuVirtUpperDomainBase⟩
/-- Its CNode. -/
def qemuVirtUntrustedCNodeId : SeLe4n.ObjId := ⟨qemuVirtUpperDomainBase + 1⟩
/-- Its VSpace. -/
def qemuVirtUntrustedVSpaceId : SeLe4n.ObjId := ⟨qemuVirtUpperDomainBase + 2⟩

/-- The core the untrusted thread is pinned to — core 1, as on the RPi5, so the
    two domains' threads start on two cores. -/
def qemuVirtUntrustedCore : SeLe4n.Kernel.Concurrency.CoreId := ⟨1, by decide⟩

/-- The untrusted domain's initial thread. -/
def qemuVirtUntrustedThread : TCB :=
  { rpi5InitialThread qemuVirtUntrustedTcbId qemuVirtUntrustedCNodeId qemuVirtUntrustedVSpaceId with
    cpuAffinity := some qemuVirtUntrustedCore }

/-- An empty user address space on `asid` whose top-level table is the
    `page`-th page of this board's table-page pool. -/
def qemuVirtInitialVSpace (asid : SeLe4n.ASID) (page : Nat) : VSpaceRoot :=
  { asid := asid, mappings := SeLe4n.Kernel.RobinHood.RHTable.empty 16
    tableBase := some (qemuVirtBootTablePage page) }

/-- The root task's untyped — the one extension the boot maps. -/
def qemuVirtRootTaskUntyped : UntypedObject :=
  rpi5InitialUntyped qemuVirtKernelReservedEnd (qemuVirtRamTop - qemuVirtKernelReservedEnd)

/-- The untyped's region is exactly the extension the boot maps. -/
theorem qemuVirtRootTaskUntyped_region :
    [(qemuVirtRootTaskUntyped.regionBase.toNat, qemuVirtRootTaskUntyped.regionSize)] =
      qemuVirtBootRamExtensions := rfl

/-- The root task's CNode: its own TCB, CNode and VSpace, the interrupt
    notification and the untyped. -/
def qemuVirtRootTaskCNode : CNode :=
  rpi5InitialCNode
    [ (SeLe4n.Slot.ofNat 1, rpi5InitialCap qemuVirtRootTaskTcbId [.read, .write, .grant, .grantReply])
    , (SeLe4n.Slot.ofNat 2, rpi5InitialCap qemuVirtRootTaskCNodeId [.read, .write, .grant, .grantReply])
    , (SeLe4n.Slot.ofNat 3, rpi5InitialCap qemuVirtRootTaskVSpaceId [.read, .write])
    , (SeLe4n.Slot.ofNat 4, rpi5InitialCap qemuVirtInterruptNotificationId [.read, .write])
    , (SeLe4n.Slot.ofNat 5, rpi5InitialCap qemuVirtRootTaskUntypedId [.read, .write, .retype]) ]

/-- The untrusted thread's CNode: its own objects and nothing of the boot
    domain's. -/
def qemuVirtUntrustedCNode : CNode :=
  rpi5InitialCNode
    [ (SeLe4n.Slot.ofNat 1, rpi5InitialCap qemuVirtUntrustedTcbId [.read, .write, .grant, .grantReply])
    , (SeLe4n.Slot.ofNat 2, rpi5InitialCap qemuVirtUntrustedCNodeId [.read, .write, .grant, .grantReply])
    , (SeLe4n.Slot.ofNat 3, rpi5InitialCap qemuVirtUntrustedVSpaceId [.read, .write]) ]

private def tcbEntry (id : SeLe4n.ObjId) (tcb : TCB) : ObjectEntry :=
  { id := id, obj := .tcb tcb
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => nomatch h }

private def cnodeEntry (id : SeLe4n.ObjId) (cn : CNode) : ObjectEntry :=
  { id := id, obj := .cnode cn
    hSlots := fun _ h => by cases h; exact CNode.slotsUnique_holds _
    hMappings := fun _ h => nomatch h }

private def vspaceEntry (id : SeLe4n.ObjId) (asid : SeLe4n.ASID) (page : Nat) : ObjectEntry :=
  { id := id, obj := .vspaceRoot (qemuVirtInitialVSpace asid page)
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => by
      cases h; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt 16 (by omega) }

private def untypedEntry (id : SeLe4n.ObjId) (ut : UntypedObject) : ObjectEntry :=
  { id := id, obj := .untyped ut
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => nomatch h }

private def notificationEntry (id : SeLe4n.ObjId) : ObjectEntry :=
  { id := id
    obj := .notification
      { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none }
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => nomatch h }

/-- The deployment's initial objects. -/
def qemuVirtInitialObjects : List ObjectEntry :=
  [ tcbEntry qemuVirtRootTaskTcbId
      (rpi5InitialThread qemuVirtRootTaskTcbId qemuVirtRootTaskCNodeId qemuVirtRootTaskVSpaceId)
  , cnodeEntry qemuVirtRootTaskCNodeId qemuVirtRootTaskCNode
  , vspaceEntry qemuVirtRootTaskVSpaceId (SeLe4n.ASID.ofNat 1) 0
  , notificationEntry qemuVirtInterruptNotificationId
  , untypedEntry qemuVirtRootTaskUntypedId qemuVirtRootTaskUntyped
  , tcbEntry qemuVirtUntrustedTcbId qemuVirtUntrustedThread
  , cnodeEntry qemuVirtUntrustedCNodeId qemuVirtUntrustedCNode
  , vspaceEntry qemuVirtUntrustedVSpaceId (SeLe4n.ASID.ofNat 2) 1 ]

/-- The IRQ table: every SPI the `virt` GICv2 carries signals the boot domain's
    notification.  SGIs and PPIs are the kernel's and are not delegated. -/
def qemuVirtIrqTable : List IrqEntry :=
  (List.range qemuVirtGicSpiCount).map fun i =>
    { irq := ⟨32 + i⟩, handler := qemuVirtInterruptNotificationId }

/-- The deployment's configuration on a board account — the caller's half.
    `bindPlatformConfig` supplies the binding's machine configuration and boot
    root. -/
def qemuVirtPlatformConfigFor (board : SeLe4n.MachineConfig) : PlatformConfig :=
  { irqTable := qemuVirtIrqTable
    initialObjects := qemuVirtInitialObjects
    machineConfig := board }

/-- The configuration the `virt` boot checks, whatever the account. -/
def qemuVirtBoundPlatformConfig : PlatformConfig :=
  { irqTable := qemuVirtIrqTable
    initialObjects := qemuVirtInitialObjects
    machineConfig := qemuVirtMachineConfig
    bootVSpaceRoot := PlatformBinding.bootVSpaceRoot (platform := QemuVirtPlatform)
    initialThreads := PlatformBinding.initialThreads (platform := QemuVirtPlatform) }

/-- Binding any account yields the one bound configuration. -/
theorem bindPlatformConfig_qemuVirtPlatformConfigFor (board : SeLe4n.MachineConfig) :
    bindPlatformConfig QemuVirtPlatform (qemuVirtPlatformConfigFor board) =
      qemuVirtBoundPlatformConfig := rfl

-- ============================================================================
-- Every gate of the checked boot, decided
-- ============================================================================

-- `virt`'s GICv2 carries 256 SPIs, so the IRQ table the duplicate and handler
-- checks walk is longer than the RPi5's 192 and the default recursion budget
-- runs out before `decide` finishes; the budget is raised for those two only.
set_option maxRecDepth 8192 in
theorem qemuVirtBoundPlatformConfig_wellFormed :
    qemuVirtBoundPlatformConfig.wellFormed = true := by
  unfold PlatformConfig.wellFormed
  rw [irqsUnique_eq_transparent, objectIdsUnique_eq_transparent]
  decide

theorem qemuVirtBoundPlatformConfig_bootSafe :
    qemuVirtBoundPlatformConfig.initialObjects.all
      (fun entry => bootSafeObjectCheck entry.obj) = true := by
  decide

theorem qemuVirtBoundPlatformConfig_asidsDistinct :
    bootVSpaceAsidsDistinct qemuVirtBoundPlatformConfig = true := by
  decide

set_option maxRecDepth 8192 in
theorem qemuVirtBoundPlatformConfig_irqHandlers :
    irqHandlersReferenceNotifications qemuVirtBoundPlatformConfig = true := by
  decide

theorem qemuVirtBoundPlatformConfig_rootDistinct :
    bootVSpaceRootObjIdDistinct qemuVirtBoundPlatformConfig = true := by
  decide

theorem qemuVirtBoundPlatformConfig_rootNonSentinel :
    bootVSpaceRootObjIdNonSentinel qemuVirtBoundPlatformConfig = true := by
  decide

theorem qemuVirtBoundPlatformConfig_rootSafe :
    bootVSpaceRootSafe qemuVirtBoundPlatformConfig = true := by
  unfold bootVSpaceRootSafe
  decide

theorem qemuVirtBoundPlatformConfig_affinities :
    bootAffinitiesDeclared (PlatformBinding.declaredCores (platform := QemuVirtPlatform))
      qemuVirtBoundPlatformConfig = true := by
  decide

theorem qemuVirtBoundPlatformConfig_physicalAddressWidth :
    qemuVirtBoundPlatformConfig.machineConfig.physicalAddressWidth ≤ 52 := by
  decide

/-- The checked boot takes its success arm on this deployment — none of its
    refusals is reachable. -/
theorem qemuVirtBoundPlatformConfig_checked :
    bootFromPlatformChecked qemuVirtBoundPlatformConfig =
      .ok (bootEnableInterruptsOp
        (installBootVSpaceRoot (bootFromPlatform qemuVirtBoundPlatformConfig)
          qemuVirtBootVSpaceRootEntry.id qemuVirtBootVSpaceRootEntry.root
          qemuVirtBootVSpaceRootEntry.hMappings)) :=
  bootFromPlatformChecked_admits_bootVSpace _ qemuVirtBoundPlatformConfig_wellFormed
    qemuVirtBoundPlatformConfig_bootSafe qemuVirtBoundPlatformConfig_asidsDistinct
    qemuVirtBoundPlatformConfig_irqHandlers qemuVirtMachineConfig_wellFormed
    qemuVirtBoundPlatformConfig_physicalAddressWidth
    qemuVirtBoundPlatformConfig_rootDistinct qemuVirtBoundPlatformConfig_rootNonSentinel
    qemuVirtBoundPlatformConfig_rootSafe qemuVirtBootVSpaceRootEntry rfl

-- ============================================================================
-- The deployment boots, with both witnesses installed and started
-- ============================================================================

/-- The idle stage: the checked boot with each core's idle thread enqueued. -/
def qemuVirtDeploymentIdleState : IntermediateState :=
  (PlatformBinding.declaredCores (platform := QemuVirtPlatform)).foldl enqueueIdleThread
    (bootEnableInterruptsOp
      (installBootVSpaceRoot (bootFromPlatform qemuVirtBoundPlatformConfig)
        qemuVirtBootVSpaceRootEntry.id qemuVirtBootVSpaceRootEntry.root
        qemuVirtBootVSpaceRootEntry.hMappings))

/-- The state the `virt` boot installs: the idle stage with both initial
    threads started. -/
def qemuVirtDeploymentBootState : IntermediateState :=
  (PlatformBinding.initialThreads (platform := QemuVirtPlatform)).foldl startInitialThread
    qemuVirtDeploymentIdleState

theorem qemuVirtBoundPlatformConfig_idleBoot :
    bootFromPlatformCheckedWithIdleThreadsFor
        (PlatformBinding.declaredCores (platform := QemuVirtPlatform))
        qemuVirtBoundPlatformConfig =
      .ok qemuVirtDeploymentIdleState :=
  bootFromPlatformCheckedWithIdleThreadsFor_map_ok _ _ _ qemuVirtBoundPlatformConfig_checked
    qemuVirtBoundPlatformConfig_affinities

private theorem qemuVirtBoundPlatformConfig_idleBoot_allCores :
    bootFromPlatformCheckedWithIdleThreads qemuVirtBoundPlatformConfig =
      .ok qemuVirtDeploymentIdleState := by
  rw [← bootFromPlatformCheckedWithIdleThreadsFor_allCores, ← qemuVirt_cores_eq_allCores]
  exact qemuVirtBoundPlatformConfig_idleBoot

private theorem qemuVirtDeployment_tcb_idle (id : SeLe4n.ObjId) (tcb : TCB)
    (hMem : tcbEntry id tcb ∈ qemuVirtInitialObjects) :
    qemuVirtDeploymentIdleState.state.getTcb? ⟨id.val⟩ = some tcb := by
  have h := bootFromPlatformCheckedWithIdleThreadsFor_ok_objects_of_mem _ _ _
    qemuVirtBoundPlatformConfig_idleBoot _ hMem
  exact (SystemState.getTcb?_eq_some_iff _ _ _).mpr h

/-- The binding's initial threads are the root task and the untrusted thread. -/
theorem qemuVirt_initialThreads :
    PlatformBinding.initialThreads (platform := QemuVirtPlatform) =
      [⟨qemuVirtRootTaskTcbId.val⟩, ⟨qemuVirtUntrustedTcbId.val⟩] := rfl

private theorem qemuVirt_initialThreads_not_idle :
    (∀ c, (⟨qemuVirtRootTaskTcbId.val⟩ : SeLe4n.ThreadId) ≠ Kernel.idleThreadId c) ∧
    (∀ c, (⟨qemuVirtUntrustedTcbId.val⟩ : SeLe4n.ThreadId) ≠ Kernel.idleThreadId c) := by
  decide

private theorem qemuVirtDeployment_initialThreads_startable :
    ∀ tid ∈ PlatformBinding.initialThreads (platform := QemuVirtPlatform),
      Kernel.initialThreadStartable qemuVirtDeploymentIdleState.state tid = true := by
  rw [qemuVirt_initialThreads]
  intro tid hMem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with h | h
  · rw [h]
    have hT := qemuVirtDeployment_tcb_idle qemuVirtRootTaskTcbId
      (rpi5InitialThread qemuVirtRootTaskTcbId qemuVirtRootTaskCNodeId qemuVirtRootTaskVSpaceId)
      (by simp [qemuVirtInitialObjects])
    exact bootFromPlatformCheckedWithIdleThreads_initialThreadStartable _ _
      qemuVirtBoundPlatformConfig_idleBoot_allCores _ _ hT
      qemuVirt_initialThreads_not_idle.1 (by decide) rfl
  · rw [h]
    have hT := qemuVirtDeployment_tcb_idle qemuVirtUntrustedTcbId qemuVirtUntrustedThread
      (by simp [qemuVirtInitialObjects])
    exact bootFromPlatformCheckedWithIdleThreads_initialThreadStartable _ _
      qemuVirtBoundPlatformConfig_idleBoot_allCores _ _ hT
      qemuVirt_initialThreads_not_idle.2 (by decide) rfl

private theorem qemuVirtDeployment_startInitialThreads :
    startInitialThreads (PlatformBinding.initialThreads (platform := QemuVirtPlatform))
        qemuVirtDeploymentIdleState = .ok qemuVirtDeploymentBootState :=
  startInitialThreads_eq_foldl _ _ (by rw [qemuVirt_initialThreads]; decide)
    qemuVirtDeployment_initialThreads_startable

/-- The started boot on the binding's cores succeeds, and this is what it
    returns. -/
theorem qemuVirtBoundPlatformConfig_boot :
    bootFromPlatformCheckedStartedFor
        (PlatformBinding.declaredCores (platform := QemuVirtPlatform))
        qemuVirtBoundPlatformConfig =
      .ok qemuVirtDeploymentBootState := by
  rw [bootFromPlatformCheckedStartedFor_of_idle _ _ _ qemuVirtBoundPlatformConfig_idleBoot]
  exact qemuVirtDeployment_startInitialThreads

/-- Both witnesses are installed on the state the boot installs, so its last
    refusal is unreachable. -/
theorem qemuVirtDeploymentBootState_witnessesInstalled :
    declaredWitnessesInstalled qemuVirtDeploymentBootState.state
      (PlatformBinding.labeling (platform := QemuVirtPlatform)) = true := by
  refine startInitialThreads_preserves_declaredWitnessesInstalled _ _ _
    qemuVirtDeployment_startInitialThreads _ ?_
  unfold declaredWitnessesInstalled
  rw [qemuVirt_deploymentLabeling_separatedThreads]
  simp only [Bool.and_eq_true]
  have h1 := qemuVirtDeployment_tcb_idle qemuVirtRootTaskTcbId
    (rpi5InitialThread qemuVirtRootTaskTcbId qemuVirtRootTaskCNodeId qemuVirtRootTaskVSpaceId)
    (by simp [qemuVirtInitialObjects])
  have h2 := qemuVirtDeployment_tcb_idle qemuVirtUntrustedTcbId qemuVirtUntrustedThread
    (by simp [qemuVirtInitialObjects])
  exact ⟨Option.isSome_iff_exists.mpr ⟨_, h1⟩, Option.isSome_iff_exists.mpr ⟨_, h2⟩⟩

/-- On the installed state both initial threads are started. -/
theorem qemuVirtDeploymentBootState_initialThreadsStarted :
    Kernel.threadStarted qemuVirtDeploymentBootState.state ⟨qemuVirtRootTaskTcbId.val⟩ ∧
    Kernel.threadStarted qemuVirtDeploymentBootState.state ⟨qemuVirtUntrustedTcbId.val⟩ := by
  have h := bootFromPlatformCheckedStartedFor_started _ _ _ qemuVirtBoundPlatformConfig_boot
  have hT : qemuVirtBoundPlatformConfig.initialThreads =
      [⟨qemuVirtRootTaskTcbId.val⟩, ⟨qemuVirtUntrustedTcbId.val⟩] := qemuVirt_initialThreads
  rw [hT] at h
  exact ⟨h _ (List.mem_cons_self ..), h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩

/-- The `virt` boot, given this deployment on **any** board account, commits the
    deployment's state and the binding's labeling and returns `.ok`. -/
theorem bootAndInitialiseQemuVirt_qemuVirtPlatformConfigFor (board : SeLe4n.MachineConfig) :
    bootAndInitialiseQemuVirt (qemuVirtPlatformConfigFor board) =
      (do
        initialiseKernelState qemuVirtDeploymentBootState.state
        initialiseKernelLabelingContext (PlatformBinding.labeling (platform := QemuVirtPlatform))
        pure (Except.ok qemuVirtDeploymentBootState.state)) := by
  rw [bootAndInitialiseQemuVirt_eq, bootAndInitialisePlatform_eq_checked_boot]
  show (match bootFromPlatformCheckedStartedFor _
      (bindPlatformConfig QemuVirtPlatform (qemuVirtPlatformConfigFor board)) with
    | .error e => _ | .ok ist => _) = _
  rw [bindPlatformConfig_qemuVirtPlatformConfigFor, qemuVirtBoundPlatformConfig_boot]
  simp only [qemuVirtDeploymentBootState_witnessesInstalled, ↓reduceIte]

/-- ...so the halting boot never halts on it. -/
theorem bootAndInitialiseQemuVirtOrHalt_qemuVirtPlatformConfigFor (board : SeLe4n.MachineConfig) :
    bootAndInitialiseQemuVirtOrHalt (qemuVirtPlatformConfigFor board) =
      (do
        initialiseKernelState qemuVirtDeploymentBootState.state
        initialiseKernelLabelingContext (PlatformBinding.labeling (platform := QemuVirtPlatform))) := by
  unfold bootAndInitialiseQemuVirtOrHalt
  rw [bootAndInitialiseQemuVirt_qemuVirtPlatformConfigFor]
  rfl

/-- The installed state satisfies the proof-layer invariant bundle, and its
    freeze the frozen one. -/
theorem qemuVirtDeploymentBootState_invariantBridge :
    SeLe4n.Kernel.Architecture.proofLayerInvariantBundle qemuVirtDeploymentBootState.state ∧
    SeLe4n.Model.apiInvariantBundle_frozen (SeLe4n.Model.freeze qemuVirtDeploymentBootState) :=
  bootToRuntime_invariantBridge_started _ PlatformBinding.declaredCores_nodup _ _
    qemuVirtBoundPlatformConfig_boot

/-- The device-tree bridge, given this deployment's half, yields
    `qemuVirtPlatformConfigFor` of the board's own account. -/
theorem qemuVirtPlatformConfigFromDtb_deployment_ok (blob : ByteArray) (config : PlatformConfig)
    (h : qemuVirtPlatformConfigFromDtb blob qemuVirtIrqTable qemuVirtInitialObjects none =
      .ok config) :
    config = qemuVirtPlatformConfigFor config.machineConfig := by
  obtain ⟨dt, -, rfl⟩ := qemuVirtPlatformConfigFromDtb_ok_eq_fromDeviceTree _ _ _ _ _ h
  rfl

/-- The root task's untyped is an object of the installed state — so the RAM
    the boot maps is the RAM the root task owns. -/
theorem qemuVirtDeploymentBootState_untypedInstalled :
    qemuVirtDeploymentBootState.state.objects[qemuVirtRootTaskUntypedId]? =
      some (.untyped qemuVirtRootTaskUntyped) :=
  startInitialThreads_objects_of_nonTcb _ _ _
    qemuVirtDeployment_startInitialThreads _ _ (fun _ h => by cases h)
    (bootFromPlatformCheckedWithIdleThreadsFor_ok_objects_of_mem _ _ _
      qemuVirtBoundPlatformConfig_idleBoot (untypedEntry qemuVirtRootTaskUntypedId
        qemuVirtRootTaskUntyped)
        (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <|
          List.mem_cons_of_mem _ <| List.mem_cons_self ..))

end SeLe4n.Platform.QemuVirt
