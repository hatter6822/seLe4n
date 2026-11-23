-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.Boot.InitialThreads

/-!
# The boot state's notification labels

The live Wait and bind admit a thread to a notification only through the
two-way `notificationFlowGate`, so no syscall puts a thread of another label on
a notification's queue or in its bound field.  A boot configuration installs
its objects as given, so the boot wrapper refuses a state whose notifications
are not label-coherent (`notificationLabelsCoherent`) before it installs
anything; that refusal is the base case of the coherence the gates keep.

This module discharges the refusal for the shipped deployments.  A
*notification-inert* object (`notificationInertObject`) names no waiter, no
bound thread and no queue neighbour, so no labeling can refuse it; every stage
of the deployment boot pipeline keeps every stored object inert when the
configuration's objects are (`bootPipeline_notificationInertObjects`), and an
inert state is coherent under every labeling
(`notificationLabelsCoherent_of_inertObjects`).
-/

namespace SeLe4n.Platform.Boot

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.RobinHood

/-- **An object no notification label check can refuse**: a notification with
no bound thread and an empty queue, a thread blocked on no notification and
carrying no notification-queue links, or any other kind of object. -/
def notificationInertObject : KernelObject → Bool
  | .notification n => n.boundTCBCode == 0 && n.waitHeadCode == 0 && n.waitTailCode == 0
  | .tcb t =>
      (match t.ipcState with
        | .blockedOnNotification _ => false
        | _ => true) && t.ntfnPrevCode == 0 && t.ntfnNextCode == 0
  | _ => true

/-- An inert object is coherent under every labeling. -/
theorem notificationEntryLabelsCoherent_of_inert (ctx : LabelingContext) (oid : SeLe4n.ObjId)
    {o : KernelObject} (h : notificationInertObject o = true) :
    notificationEntryLabelsCoherent ctx oid o = true := by
  cases o with
  | notification n =>
    simp only [notificationInertObject, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hB, hH⟩, hT⟩ := h
    simp [notificationEntryLabelsCoherent, Notification.boundTCB, Notification.waitHead,
      Notification.waitTail, hB, hH, hT]
  | tcb t =>
    simp only [notificationInertObject, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hI, hP⟩, hN⟩ := h
    unfold notificationEntryLabelsCoherent
    dsimp only
    split
    · next nid hIpc => simp only [hIpc] at hI; cases hI
    · simp [hP, hN]
  | _ => rfl

/-- **Every stored object is notification-inert.** -/
@[reducible] def NotificationInertObjects (st : SystemState) : Prop :=
  ∀ (k : SeLe4n.ObjId) (o : KernelObject), st.objects[k]? = some o →
    notificationInertObject o = true

/-- An inert state is coherent under every labeling. -/
theorem notificationLabelsCoherent_of_inertObjects {st : SystemState}
    (hExt : st.objects.invExt) (h : NotificationInertObjects st) (ctx : LabelingContext) :
    notificationLabelsCoherent st ctx = true :=
  RHTable.fold_and_true_of_forall_get? st.objects _ hExt fun k _ hk =>
    notificationEntryLabelsCoherent_of_inert ctx k (h k _ hk)

/-- Clearing run-queue fields keeps inertness. -/
theorem notificationInertObject_withoutRunLinks (o : KernelObject) :
    notificationInertObject o.withoutRunLinks = notificationInertObject o := by
  cases o <;> rfl

/-- Clearing derivation links keeps inertness. -/
theorem notificationInertObject_withoutLinks (o : KernelObject) :
    notificationInertObject o.withoutLinks = notificationInertObject o := by
  cases o <;> rfl

/-- Storing an inert object keeps every object inert. -/
theorem NotificationInertObjects.insert {st : SystemState} (hExt : st.objects.invExt)
    (h : NotificationInertObjects st) {k : SeLe4n.ObjId} {v : KernelObject}
    (hv : notificationInertObject v = true) :
    NotificationInertObjects { st with objects := st.objects.insert k v } := by
  intro k' o hk'
  simp only [RHTable_getElem?_eq_get?] at hk'
  by_cases hEq : k = k'
  · subst hEq
    rw [RHTable.getElem?_insert_self _ _ _ hExt] at hk'
    cases hk'; exact hv
  · rw [RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hEq (eq_of_beq hb)) hExt] at hk'
    exact h k' o (by simpa only [RHTable_getElem?_eq_get?] using hk')

/-- Inertness transfers across a step that writes only run-queue fields. -/
theorem NotificationInertObjects.of_agreeOffRunLinks {st st' : SystemState}
    (hA : SystemState.objectsAgreeOffRunLinks st' st) (h : NotificationInertObjects st) :
    NotificationInertObjects st' := by
  intro k o hk
  have e := hA k
  rw [hk] at e
  cases hS : st.objects[k]? with
  | none => rw [hS] at e; cases e
  | some o0 =>
    rw [hS] at e
    simp only [Option.map_some, Option.some.injEq] at e
    rw [← notificationInertObject_withoutRunLinks, e, notificationInertObject_withoutRunLinks]
    exact h k o0 hS

/-- Inertness transfers across a step that writes only derivation links. -/
theorem NotificationInertObjects.of_agreeOffDerivationLinks {st st' : SystemState}
    (hA : SystemState.objectsAgreeOffDerivationLinks st' st) (h : NotificationInertObjects st) :
    NotificationInertObjects st' := by
  intro k o hk
  have e := (hA k).map_withoutLinks
  rw [hk] at e
  cases hS : st.objects[k]? with
  | none => rw [hS] at e; cases e
  | some o0 =>
    rw [hS] at e
    simp only [Option.map_some, Option.some.injEq] at e
    rw [← notificationInertObject_withoutLinks, e, notificationInertObject_withoutLinks]
    exact h k o0 hS

/-! ## The deployment boot pipeline keeps every object inert -/

/-- The plain boot stores only configured objects. -/
theorem bootFromPlatform_notificationInertObjects (config : PlatformConfig)
    (hCfg : ∀ e ∈ config.initialObjects, notificationInertObject e.obj = true) :
    NotificationInertObjects (bootFromPlatform config).state := by
  intro k o hk
  obtain ⟨e, he, -, rfl⟩ := bootFromPlatform_objects_of_config config k o hk
  exact hCfg e he

/-- The boot VSpace root is inert. -/
theorem installBootVSpaceRoot_notificationInertObjects (ist : IntermediateState)
    (id : SeLe4n.ObjId) (vsr : VSpaceRoot) (hM : vsr.mappings.invExt)
    (h : NotificationInertObjects ist.state) :
    NotificationInertObjects (installBootVSpaceRoot ist id vsr hM).state := by
  intro k o hk
  by_cases hEq : id = k
  · subst hEq
    rw [installBootVSpaceRoot_objects_lookup] at hk
    cases hk; rfl
  · rw [installBootVSpaceRoot_objects_ne _ _ _ _ _ hEq] at hk
    exact h k o hk

/-- Enabling interrupts writes no object. -/
theorem bootEnableInterruptsOp_notificationInertObjects (ist : IntermediateState)
    (h : NotificationInertObjects ist.state) :
    NotificationInertObjects (bootEnableInterruptsOp ist).state := by
  intro k o hk
  rw [bootEnableInterruptsOp_objects_eq] at hk
  exact h k o hk

/-- The idle threads are inert. -/
theorem foldl_storeIdleThread_notificationInertObjects
    (L : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState)
    (h : NotificationInertObjects ist.state) :
    NotificationInertObjects (L.foldl storeIdleThread ist).state := by
  intro k o hk
  rcases foldl_storeIdleThread_objects_cases L ist k o hk with hPre | ⟨c, -, rfl⟩
  · exact h k o hPre
  · rfl

/-- Starting a thread writes its scheduling state, its IPC state (`.ready`)
and its run-queue fields: an inert thread stays inert. -/
theorem startInitialThreadOnCore_notificationInertObjects (st : SystemState)
    (tid : SeLe4n.ThreadId) (hExt : st.objects.invExt) (h : NotificationInertObjects st) :
    NotificationInertObjects (startInitialThreadOnCore st tid) := by
  cases hT : st.getTcb? tid with
  | none => rw [startInitialThreadOnCore_eq_of_none hT]; exact h
  | some tcb =>
    have hTcb : notificationInertObject (.tcb tcb) = true :=
      h _ _ ((SystemState.getTcb?_eq_some_iff st tid tcb).mp hT)
    have hReady : notificationInertObject (.tcb { tcb with threadState := .Ready }) = true :=
      hTcb
    cases hF : startFresh st tid with
    | false =>
      rw [startInitialThreadOnCore_eq_of_declined hT hF hExt]
      exact h.insert hExt hReady
    | true =>
      have hStarted : notificationInertObject (.tcb (startedThread tcb)) = true := by
        simp only [notificationInertObject, Bool.and_eq_true, beq_iff_eq] at hTcb ⊢
        exact ⟨⟨rfl, hTcb.1.2⟩, hTcb.2⟩
      refine NotificationInertObjects.of_agreeOffRunLinks
        (startInitialThreadOnCore_objectsAgree hT hF hExt) ?_
      exact (h.insert hExt hReady).insert (RHTable_insert_preserves_invExt _ _ _ hExt) hStarted

/-- Starting the initial threads keeps every object inert. -/
theorem foldl_startInitialThread_notificationInertObjects (L : List SeLe4n.ThreadId)
    (ist : IntermediateState) (h : NotificationInertObjects ist.state) :
    NotificationInertObjects (L.foldl startInitialThread ist).state := by
  induction L generalizing ist with
  | nil => exact h
  | cons t ts ih =>
    exact ih _ (startInitialThreadOnCore_notificationInertObjects ist.state t
      ist.hAllTables.objects.1 h)

/-- The interrupt nodes are inert. -/
theorem installIrqNodes_notificationInertObjects (n : Nat) (ist : IntermediateState)
    (h : NotificationInertObjects ist.state) :
    NotificationInertObjects (installIrqNodes n ist).state := by
  intro k o hk
  rw [installIrqNodes_objects] at hk
  split at hk
  · cases hk; rfl
  · exact h k o hk

/-- The root server's objects are inert, and its thread keeps its IPC state and
its notification-queue links. -/
theorem installRootServer_notificationInertObjects (config : PlatformConfig)
    (ist : IntermediateState) (h : NotificationInertObjects ist.state) :
    NotificationInertObjects (installRootServer config ist).state := by
  intro k o hk
  rcases installRootServer_objects_cases config ist k with e | ⟨r, -, hCases⟩
  · rw [e] at hk; exact h k o hk
  · rcases hCases with ⟨-, hF | ⟨vsId, l, hF⟩⟩ | ⟨vs, -, hF⟩ | ⟨cn, asid, -, hF⟩ |
        ⟨t, -, hPre, hF⟩
    · rw [hF] at hk; cases hk; rfl
    · rw [hF] at hk; cases hk; rfl
    · rw [hF] at hk; cases hk; rfl
    · rw [hF] at hk; cases hk; rfl
    · rw [hF] at hk; cases hk
      exact (h k _ hPre : notificationInertObject (.tcb t) = true)

/-- Linking the boot capabilities writes only derivation links. -/
theorem linkBootCapabilities_notificationInertObjects (config : PlatformConfig)
    (ist : IntermediateState) (h : NotificationInertObjects ist.state) :
    NotificationInertObjects (linkBootCapabilities config ist).state :=
  NotificationInertObjects.of_agreeOffDerivationLinks (linkBootCapabilities_agree config ist) h

/-- **The deployment boot pipeline keeps every object inert** when the
configuration's objects are: the plain boot, the boot VSpace root, interrupt
enable, the idle threads, the initial threads' start, the interrupt nodes, the
root server and the capability links, in the order the deployments run them. -/
theorem bootPipeline_notificationInertObjects (config : PlatformConfig)
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (threads : List SeLe4n.ThreadId)
    (n : Nat) (id : SeLe4n.ObjId) (vsr : VSpaceRoot) (hM : vsr.mappings.invExt)
    (hCfg : ∀ e ∈ config.initialObjects, notificationInertObject e.obj = true) :
    NotificationInertObjects
      (linkBootCapabilities config
        (installRootServer config
          (installIrqNodes n
            (threads.foldl startInitialThread
              (cores.foldl storeIdleThread
                (bootEnableInterruptsOp
                  (installBootVSpaceRoot (bootFromPlatform config) id vsr hM))))))).state :=
  linkBootCapabilities_notificationInertObjects _ _ <|
  installRootServer_notificationInertObjects _ _ <|
  installIrqNodes_notificationInertObjects _ _ <|
  foldl_startInitialThread_notificationInertObjects _ _ <|
  foldl_storeIdleThread_notificationInertObjects _ _ <|
  bootEnableInterruptsOp_notificationInertObjects _ <|
  installBootVSpaceRoot_notificationInertObjects _ _ _ _ <|
  bootFromPlatform_notificationInertObjects config hCfg

end SeLe4n.Platform.Boot
