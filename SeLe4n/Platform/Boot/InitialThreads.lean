-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.Boot
import SeLe4n.Platform.Boot.CapabilityLinks
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement

/-!
# WS-BP BP7.11 — the boot starts its designated threads

The checked, idle-storing boot (`bootFromPlatformCheckedWithIdleThreadsFor`)
installs every configured thread `.Inactive` and queues nothing (each declared
core's idle thread is stored, never queued), so until this stage no deployment
thread ever ran:
nothing held a capability to either initial thread's TCB outside that thread's
own CSpace, and nothing resumed it.  This module is the stage after the idle
store that **starts** the threads a configuration names
(`PlatformConfig.initialThreads`) — each through the kernel model's own start
(`Kernel.startInitialThreadOnCore`), so it is `.Ready` and queued on its home
core, and each core's first scheduling point dispatches it; idle runs only
when its core's queue is empty.  A platform binding names the threads its hardware boot starts
(`Platform.FFI.bindPlatformConfig`): the labeling's two separation witnesses,
one per domain, so the witnesses the labeling guard is decided on are threads
that run.

Three things it establishes, each over the stage rather than one config:

* **it refuses rather than skips** — a named thread the boot cannot start
  (absent, not `.Inactive`, already queued, a zero time slice, an inherited
  boost) refuses the boot, and a thread named twice is refused at its second
  occurrence;
* **the bundle** — the started state is of boot shape
  (`bootStartShape`), so the proof-layer bundle and the frozen bundle hold of
  it by the same argument as the idle boot's (`bootToRuntime_invariantBridge_started`);
* **the classification** — the full thread-state classification survives every
  start (`Kernel.startInitialThreadOnCore_preserves_threadStateConsistent`), and
  every named thread is queued and stored `.Ready`
  (`startInitialThreads_ok_started`).

With no named thread the stage is the identity
(`bootFromPlatformCheckedStartedFor_of_nil`), so every theorem about the idle
boot is a theorem about the started boot of a configuration that names none.
-/

namespace SeLe4n.Platform.Boot

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency (bootCoreId)

-- ============================================================================
-- §1  The stage
-- ============================================================================

/-- **WS-BP BP7.11**: start `tid` on a boot `IntermediateState` — the kernel
model's start on the state, and its four structural witnesses carried by that
operation's own preservation theorems (the shape `storeIdleThread` takes). -/
def startInitialThread (ist : IntermediateState) (tid : SeLe4n.ThreadId) :
    IntermediateState where
  state := startInitialThreadOnCore ist.state tid
  hAllTables := startInitialThreadOnCore_preserves_allTablesInvExtK ist.state tid ist.hAllTables
  hPerObjectSlots := startInitialThreadOnCore_preserves_perObjectSlotsInvariant ist.state tid
    ist.hAllTables.objects.1 ist.hPerObjectSlots
  hPerObjectMappings := startInitialThreadOnCore_preserves_perObjectMappingsInvariant ist.state tid
    ist.hAllTables.objects.1 ist.hPerObjectMappings
  hLifecycleConsistent := startInitialThreadOnCore_preserves_objectTypeMetadataConsistent
    ist.state tid ist.hAllTables.objects.1 ist.hLifecycleConsistent

/-- **WS-BP BP7.11** (the derivation, pinned): the boot's start *is* the kernel
model's, on the intermediate state's `state`. -/
theorem startInitialThread_state (ist : IntermediateState) (tid : SeLe4n.ThreadId) :
    (startInitialThread ist tid).state = startInitialThreadOnCore ist.state tid := rfl

/-- **WS-BP BP7.11**: the boot error for a named thread the boot cannot start. -/
def unstartableInitialThreadBootError : String :=
  "boot: a designated initial thread is not a stored, inactive, unqueued thread " ++
  "with a positive time slice and no inherited boost (WS-BP BP7.11)"

/-- **WS-BP BP7.11**: start each named thread in order, refusing the boot at the
first that `initialThreadStartable` does not admit. -/
def startInitialThreads : List SeLe4n.ThreadId → IntermediateState →
    Except String IntermediateState
  | [], ist => .ok ist
  | tid :: rest, ist =>
      if initialThreadStartable ist.state tid then
        startInitialThreads rest (startInitialThread ist tid)
      else
        .error unstartableInitialThreadBootError

/-- **WS-BP BP7.11**: the boot's started stage over a declared core list — the
idle-storing boot, then the configuration's named threads started, then
(WS-ZA ZA5.4) the configuration's capabilities linked into the derivation tree
(`linkBootCapabilities`). -/
def bootFromPlatformCheckedStartedFor
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig) :
    Except String IntermediateState :=
  (bootFromPlatformCheckedWithIdleThreadsFor cores config).bind fun base =>
    (startInitialThreads config.initialThreads base).map (linkBootCapabilities config)

-- ============================================================================
-- §2  The stage's shape
-- ============================================================================

/-- **WS-BP BP7.11**: a property every start keeps is a property of the stage. -/
theorem startInitialThreads_induct (P : IntermediateState → Prop)
    (hStep : ∀ ist tid, initialThreadStartable ist.state tid = true → P ist →
      P (startInitialThread ist tid)) :
    ∀ (L : List SeLe4n.ThreadId) (ist ist' : IntermediateState),
      startInitialThreads L ist = .ok ist' → P ist → P ist' := by
  intro L
  induction L with
  | nil => intro ist ist' h hP; cases h; exact hP
  | cons tid rest ih =>
    intro ist ist' h hP
    unfold startInitialThreads at h
    split at h
    · exact ih _ _ h (hStep ist tid (by assumption) hP)
    · cases h

/-- **WS-BP BP7.11**: with no named thread the stage is the idle boot with its
capabilities linked. -/
theorem bootFromPlatformCheckedStartedFor_of_nil
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (h : config.initialThreads = []) :
    bootFromPlatformCheckedStartedFor cores config =
      (bootFromPlatformCheckedWithIdleThreadsFor cores config).map (linkBootCapabilities config) := by
  unfold bootFromPlatformCheckedStartedFor
  rw [h]
  cases bootFromPlatformCheckedWithIdleThreadsFor cores config <;> rfl

/-- **WS-BP BP7.11**: the stage rejects everything the checked boot rejects. -/
theorem bootFromPlatformCheckedStartedFor_rejects_invalid
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig) (e : String)
    (h : bootFromPlatformChecked config = .error e) :
    bootFromPlatformCheckedStartedFor cores config = .error e := by
  unfold bootFromPlatformCheckedStartedFor
  rw [bootFromPlatformCheckedWithIdleThreadsFor_rejects_invalid cores config e h]
  rfl

/-- **WS-BP BP7.11**: after a successful idle boot, the stage is the starts and
the linking — stated over variables, so a concrete configuration rewrites with
it instead of unfolding the bind against its own boot state. -/
theorem bootFromPlatformCheckedStartedFor_of_idle
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (base : IntermediateState)
    (h : bootFromPlatformCheckedWithIdleThreadsFor cores config = .ok base) :
    bootFromPlatformCheckedStartedFor cores config =
      (startInitialThreads config.initialThreads base).map (linkBootCapabilities config) := by
  unfold bootFromPlatformCheckedStartedFor
  rw [h]
  rfl

/-- **WS-BP BP7.11**: a successful stage is a successful idle boot followed by a
successful start of every named thread, its capabilities then linked. -/
theorem bootFromPlatformCheckedStartedFor_ok
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor cores config = .ok ist) :
    ∃ base started, bootFromPlatformCheckedWithIdleThreadsFor cores config = .ok base ∧
      startInitialThreads config.initialThreads base = .ok started ∧
      ist = linkBootCapabilities config started := by
  unfold bootFromPlatformCheckedStartedFor at h
  cases hB : bootFromPlatformCheckedWithIdleThreadsFor cores config with
  | error e => rw [hB] at h; cases h
  | ok base =>
    rw [hB] at h
    change Except.map _ (startInitialThreads config.initialThreads base) = _ at h
    cases hS : startInitialThreads config.initialThreads base with
    | error e => rw [hS] at h; cases h
    | ok started =>
      rw [hS] at h
      cases h
      exact ⟨base, started, rfl, hS, rfl⟩

-- ============================================================================
-- §3  The bundle
-- ============================================================================

/-- WS-ZA ZA4.6: a slot's reply-waiter link codes — the four TCB fields the
start never writes (its flag, its `.ready` mark and its run-queue links leave
them). -/
def replyLinkCodes : Option ReplyView → Option (Nat × Nat × Nat × Nat) :=
  Option.map fun v => (v.prevCode, v.nextCode, v.headCode, v.count)

/-- WS-ZA ZA4.6: overwriting a TCB with one of the same link codes keeps every
slot's link codes. -/
theorem replyLinkCodes_insert_tcb (st : SystemState) (hInv : st.objects.invExt)
    {k : SeLe4n.ObjId} {t t' : TCB} (hOld : st.objects[k]? = some (.tcb t))
    (hc : replyLinkCodes (some t'.replyView) = replyLinkCodes (some t.replyView))
    (j : SeLe4n.ObjId) :
    replyLinkCodes (objReplyView (st.objects.insert k (.tcb t'))[j]?) =
      replyLinkCodes (st.replyViews j) := by
  unfold SystemState.replyViews SystemState.getObject?
  by_cases h : k = j
  · subst h
    change replyLinkCodes (objReplyView ((st.objects.insert k _).get? k)) = _
    rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self _ _ _ hInv, hOld]; exact hc
  · change replyLinkCodes (objReplyView ((st.objects.insert k _).get? j)) = _
    rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (by simpa using h) hInv]; rfl

/-- WS-ZA ZA4.6: the start keeps every slot's reply-waiter link codes. -/
theorem startInitialThreadOnCore_replyLinkCodes (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (j : SeLe4n.ObjId) :
    replyLinkCodes ((startInitialThreadOnCore st tid).replyViews j) =
      replyLinkCodes (st.replyViews j) := by
  have hU : ∀ j, replyLinkCodes ((st.updateTcb tid fun t =>
      { t with threadState := .Ready }).replyViews j) = replyLinkCodes (st.replyViews j) := by
    intro j
    cases hT : st.getTcb? tid with
    | none => rw [SystemState.updateTcb_eq_self_of_none hT]
    | some t =>
      rw [SystemState.updateTcb_eq_of_some hT]
      exact replyLinkCodes_insert_tcb st hInv (t' := { t with threadState := .Ready })
        ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) rfl j
  have hInv1 := SystemState.updateTcb_preserves_objects_invExt st tid
    (fun t => { t with threadState := .Ready }) hInv
  unfold startInitialThreadOnCore enqueueRunnableOnCore
  generalize st.updateTcb tid (fun t => { t with threadState := .Ready }) = s1 at hU hInv1
  split
  · rename_i tcb h _
    split
    · exact hU j
    · show replyLinkCodes ((SystemState.runEnqueueAdmitted _ _ tid _).replyViews j) = _
      rw [SystemState.runEnqueueAdmitted_replyViews_eq, ← hU j]
      exact replyLinkCodes_insert_tcb s1 hInv1 (t' := (tcb.setIpcState .ready))
        ((SystemState.getTcb?_eq_some_iff _ _ _).mp h) rfl j
  · exact hU j

/-- WS-ZA ZA5.4 part 27: overwriting a TCB with one of the same
bound-notification code keeps every slot's binding codes. -/
theorem sameNotificationBindings_insert_tcb (st : SystemState) (hInv : st.objects.invExt)
    {k : SeLe4n.ObjId} {t t' : TCB} (hOld : st.objects[k]? = some (.tcb t))
    (hc : t'.boundNotificationCode = t.boundNotificationCode) :
    sameNotificationBindings st { st with objects := st.objects.insert k (.tcb t') } := by
  intro j
  by_cases h : k = j
  · subst h
    show notificationBindingCodes ((st.objects.insert k _).get? k) = _
    rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self _ _ _ hInv, hOld]
    simp only [notificationBindingCodes, KernelObject.bindingCodes, hc]
  · show notificationBindingCodes ((st.objects.insert k _).get? j) = _
    rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (by simpa using h) hInv]; rfl

/-- WS-ZA ZA5.4 part 27: the start keeps every slot's notification-binding
codes — it writes the thread's state, its IPC state and its run links. -/
theorem startInitialThreadOnCore_sameNotificationBindings (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    sameNotificationBindings st (startInitialThreadOnCore st tid) := by
  have hU : sameNotificationBindings st
      (st.updateTcb tid fun t => { t with threadState := .Ready }) := by
    cases hT : st.getTcb? tid with
    | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact .refl _
    | some t =>
      rw [SystemState.updateTcb_eq_of_some hT]
      exact sameNotificationBindings_insert_tcb st hInv (t' := { t with threadState := .Ready })
        ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) rfl
  have hInv1 := SystemState.updateTcb_preserves_objects_invExt st tid
    (fun t => { t with threadState := .Ready }) hInv
  unfold startInitialThreadOnCore enqueueRunnableOnCore
  generalize st.updateTcb tid (fun t => { t with threadState := .Ready }) = s1 at hU hInv1
  split
  · rename_i tcb h _
    split
    · exact hU
    · refine hU.trans ((sameNotificationBindings_insert_tcb s1 hInv1
        (t' := tcb.setIpcState .ready) ((SystemState.getTcb?_eq_some_iff _ _ _).mp h) rfl).trans
        (.of_objectsAgreeOffRunLinks (SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks _ _ _ _)))
  · exact hU

/-- The start keeps the table references: it writes the thread's state and
its run-queue links. -/
theorem startInitialThreadOnCore_tableReferenceFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    SystemState.TableReferenceFrame st (startInitialThreadOnCore st tid) := by
  have hInv1 := SystemState.updateTcb_preserves_objects_invExt st tid
    (fun t => { t with threadState := .Ready }) hInv
  unfold startInitialThreadOnCore
  exact (SystemState.TableReferenceFrame.updateTcb st tid _ hInv).trans
    (.of_kindPreservingWrite (enqueueRunnableOnCore_kindPreservingWrite _ _ tid hInv1)
      (enqueueRunnableOnCore_onlyObjectsSchedulerDiffer _ _ tid).referenceTables)

/-- **WS-BP BP7.11**: **a start keeps the boot shape.**  The written TCB was
boot-shaped and the start moves only its flag and its IPC state to `.ready`;
nothing else in the object store moves, so the ASID table, the untypeds and
the quiescent fields are as they were; the scheduler gains one run-queue
member; and the boot core's queue stays boot-sound
(`Kernel.startInitialThreadOnCore_preserves_runQueueBootSound`). -/
theorem startInitialThread_preserves_bootStartShape (ist : IntermediateState)
    (tid : SeLe4n.ThreadId) (hStart : initialThreadStartable ist.state tid = true)
    (h : bootStartShape ist) : bootStartShape (startInitialThread ist tid) := by
  have hInv := ist.hAllTables.objects.1
  obtain ⟨hShape, hFields, hAsid, hUntyped, ⟨rq, re, rp, hSch⟩, hRun, hQueue, hBindings, hTab⟩ :=
    h
  have hFrame := startInitialThreadOnCore_frame ist.state tid
  refine ⟨?_, ?_, ?_, ?_, ?_, startInitialThreadOnCore_runQueueRefined ist.state tid hInv hRun, ?_,
    .of_codes (startInitialThreadOnCore_sameNotificationBindings ist.state tid hInv) hBindings,
    (startInitialThreadOnCore_tableReferenceFrame ist.state tid hInv).preserves hTab⟩
  · intro oid obj hObj
    rcases startInitialThreadOnCore_objects_cases ist.state tid hInv oid obj hObj with
      hB | ⟨t, t', hT, rfl, he⟩
    · exact hShape oid obj hB
    · obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, -, hC⟩ := hShape oid _ hT
      refine ⟨⟨fun _ e => (by cases e), fun _ e => (by cases e), fun _ e => (by cases e),
        fun x hx => ?_, fun _ e => (by cases e), fun _ e => (by cases e), fun _ e => (by cases e)⟩,
        fun _ e => (by cases e), fun x hx => ?_⟩ <;> cases hx
      rotate_left
      · rcases he with he | he | he <;>
        exact (TCB.proj_eq_of_withoutRunLinks_eq TCB.spaceLinksClear he).trans (hC t rfl)
      obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15⟩ := h4 t rfl
      -- The start writes the thread's state, its IPC state (to `.ready`) and
      -- its run-queue links; every shape field reads past all three, and the
      -- reply-waiter link codes are untouched (`startInitialThreadOnCore_replyLinkCodes`).
      have hc := startInitialThreadOnCore_replyLinkCodes ist.state tid hInv oid
      rw [SystemState.replyViews, SystemState.replyViews, SystemState.getObject?, SystemState.getObject?, show (startInitialThreadOnCore ist.state tid).objects[oid]? = _ from hObj, hT] at hc
      simp only [objReplyView_tcb, replyLinkCodes, Option.map_some, Option.some.injEq,
        Prod.mk.injEq, TCB.replyView] at hc
      obtain ⟨c1, c2, c3, c4⟩ := hc
      have r1 : t'.replyWaiterPrev = none := by
        simp only [TCB.replyWaiterPrev, c1]; exact t12
      have r2 : t'.replyWaiterNext = none := by
        simp only [TCB.replyWaiterNext, c2]; exact t13
      have r3 : t'.replyWaitersHead = none := by
        simp only [TCB.replyWaitersHead, c3]; exact t14
      have r4 : t'.replyWaitersCount = 0 := c4.trans t15.1
      rcases he with he | he | he <;>
      exact ⟨(TCB.proj_eq_of_withoutRunLinks_eq TCB.pendingMessage he).trans t1,
        (TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState he).trans (by first | exact t2 | rfl),
        (TCB.proj_eq_of_withoutRunLinks_eq TCB.queueNext he).trans t3,
        (TCB.proj_eq_of_withoutRunLinks_eq TCB.queuePrev he).trans t4,
        (TCB.proj_eq_of_withoutRunLinks_eq TCB.queuePPrev he).trans t5,
        (TCB.proj_eq_of_withoutRunLinks_eq TCB.timeoutBudget he).trans t6,
        (TCB.proj_eq_of_withoutRunLinks_eq TCB.schedContextBinding he).trans t7,
        (TCB.proj_eq_of_withoutRunLinks_eq TCB.replyObject he).trans t8,
        (TCB.proj_eq_of_withoutRunLinks_eq TCB.pendingReceiveReply he).trans t9,
        (TCB.proj_eq_of_withoutRunLinks_eq TCB.ntfnPrev he).trans t10,
        (TCB.proj_eq_of_withoutRunLinks_eq TCB.ntfnNext he).trans t11, r1, r2, r3, r4,
        bootSpaceSlotCapsSafe_of_cells_eq (TCB.proj_eq_of_withoutRunLinks_eq TCB.spaceCells he)
          t15.2.1, (TCB.proj_eq_of_withoutRunLinks_eq TCB.yieldToCode he).trans t15.2.2⟩
  · show bootQuiescentFields (startInitialThreadOnCore ist.state tid)
    rw [hFrame]; exact hFields
  · show Architecture.asidTableConsistent (startInitialThreadOnCore ist.state tid)
    obtain ⟨hA1, hA2⟩ := hAsid
    refine ⟨?_, ?_⟩
    · intro asid oid hEntry
      rw [hFrame] at hEntry
      obtain ⟨root, hRoot, hAsidEq⟩ := hA1 asid oid hEntry
      exact ⟨root, startInitialThreadOnCore_objects_of_nonTcb _ _ hInv _ _
        (fun t hc => by cases hc) hRoot, hAsidEq⟩
    · intro oid root hRoot
      rcases startInitialThreadOnCore_objects_cases ist.state tid hInv oid _ hRoot with
        hB | ⟨_, _, _, hc, _⟩
      · rw [hFrame]; exact hA2 oid root hB
      · cases hc
  · show Kernel.untypedRegionsDisjoint (startInitialThreadOnCore ist.state tid)
    refine untypedRegionsDisjoint_of_untyped_subset hUntyped ?_
    intro oid ut hObj
    rcases startInitialThreadOnCore_objects_cases ist.state tid hInv oid _ hObj with
      hB | ⟨_, _, _, hc, _⟩
    · exact hB
    · cases hc
  · obtain ⟨rq', re', rp', hrq'⟩ :=
      startInitialThreadOnCore_scheduler_runQueueOnly ist.state tid
    refine ⟨rq', re', rp', ?_⟩
    show (startInitialThreadOnCore ist.state tid).scheduler = _
    rw [hrq', hSch]
  · exact startInitialThreadOnCore_preserves_runQueueBootSound hStart hInv hRun bootCoreId hQueue

/-- **WS-ZA ZA5.4**: a start writes no capability slot: the thread it writes
keeps its space slots, so a slot holding a capability after it held the same
one before. -/
theorem startInitialThreadOnCore_slotCapAt_of_ne_none (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (r : SlotRef)
    (h : (startInitialThreadOnCore st tid).slotCapAt r ≠ none) :
    (startInitialThreadOnCore st tid).slotCapAt r = st.slotCapAt r := by
  rw [SystemState.slotCapAt_eq_bind] at h ⊢
  rw [SystemState.slotCapAt_eq_bind]
  cases hO : (startInitialThreadOnCore st tid).objects[r.cnode]? with
  | none => rw [hO] at h; exact absurd rfl h
  | some o =>
    rcases startInitialThreadOnCore_objects_cases st tid hInv r.cnode o hO with
      hB | ⟨t, t', hT, rfl, hw⟩
    · rw [hB]
    · rw [hT]
      have hc : t'.spaceCells = t.spaceCells := by
        rcases hw with hw | hw | hw
        · exact TCB.proj_eq_of_withoutRunLinks_eq TCB.spaceCells hw
        · exact TCB.proj_eq_of_withoutRunLinks_eq TCB.spaceCells hw
        · exact TCB.proj_eq_of_withoutRunLinks_eq TCB.spaceCells hw
      simp only [Option.bind_some, KernelObject.slotCap, TCB.spaceSlotCap, hc]

theorem startInitialThreadOnCore_slotCapAt_ne_none (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (r : SlotRef)
    (h : (startInitialThreadOnCore st tid).slotCapAt r ≠ none) : st.slotCapAt r ≠ none := by
  rw [← startInitialThreadOnCore_slotCapAt_of_ne_none st tid hInv r h]; exact h

/-- **WS-ZA ZA5.4 part 18**: a start removes no object. -/
theorem startInitialThreadOnCore_objectPresent (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (h : st.objectPresent k) :
    (startInitialThreadOnCore st tid).objectPresent k := by
  obtain ⟨obj, hO⟩ := Option.ne_none_iff_exists'.mp h
  by_cases hT : ∃ t, obj = .tcb t
  · obtain ⟨t, rfl⟩ := hT
    have hG : (st.getTcb? (SeLe4n.ThreadId.ofObjId k)).isSome = true := by
      rw [Option.isSome_iff_exists]
      exact ⟨t, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO⟩
    obtain ⟨t', hT'⟩ := Option.isSome_iff_exists.mp
      (startInitialThreadOnCore_getTcb?_isSome st tid _ hInv hG)
    have e := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT'
    show (startInitialThreadOnCore st tid).objects[k]? ≠ none
    rw [SeLe4n.ThreadId.toObjId_ofObjId] at e
    rw [e]; exact Option.some_ne_none _
  · show (startInitialThreadOnCore st tid).objects[k]? ≠ none
    rw [startInitialThreadOnCore_objects_of_nonTcb st tid hInv k obj
      (fun t e => hT ⟨t, e⟩) hO]
    exact Option.some_ne_none _

/-- **WS-ZA ZA5.4 part 18**: the starts keep every capability naming a live
object: they write no capability slot and remove no object. -/
theorem startInitialThreads_capabilitiesLive (L : List SeLe4n.ThreadId)
    (ist ist' : IntermediateState) (h : startInitialThreads L ist = .ok ist')
    (hL : ∀ r o, SystemState.namesAt ist.state.slotCapAt r o → ist.state.objectPresent o) :
    ∀ r o, SystemState.namesAt ist'.state.slotCapAt r o → ist'.state.objectPresent o :=
  startInitialThreads_induct
    (fun i => ∀ r o, SystemState.namesAt i.state.slotCapAt r o → i.state.objectPresent o)
    (fun i tid _ hP r o hN => by
      have hInv := i.hAllTables.objects.1
      rw [startInitialThread_state] at hN ⊢
      rw [SystemState.namesAt_of_eq (startInitialThreadOnCore_slotCapAt_of_ne_none i.state tid
        hInv r (SystemState.namesAt_occupied hN))] at hN
      exact startInitialThreadOnCore_objectPresent i.state tid hInv o (hP r o hN))
    L ist ist' h hL

/-- **WS-ZA ZA5.4 part 19**: a start keeps every untyped record: it writes a
thread over a thread and removes no object. -/
theorem startInitialThreadOnCore_getUntyped? (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    (startInitialThreadOnCore st tid).getUntyped? = st.getUntyped? := by
  funext k
  rw [SystemState.getUntyped?_eq_bind, SystemState.getUntyped?_eq_bind]
  cases hO : (startInitialThreadOnCore st tid).objects[k]? with
  | none =>
    cases hP : st.objects[k]? with
    | none => rfl
    | some o =>
      exact absurd hO (startInitialThreadOnCore_objectPresent st tid hInv k
        (show st.objects[k]? ≠ none by rw [hP]; simp))
  | some o =>
    rcases startInitialThreadOnCore_objects_cases st tid hInv k o hO with hB | ⟨_, _, hT, rfl, _⟩
    · rw [hB]
    · rw [hT]; rfl

/-- **WS-ZA ZA5.4 part 19**: the starts keep each untyped named from one slot at
most and recording no child: they write no capability slot and no untyped. -/
theorem startInitialThreads_untypedsSole (L : List SeLe4n.ThreadId)
    (ist ist' : IntermediateState) (h : startInitialThreads L ist = .ok ist')
    (hL : (∀ u r r', SystemState.untypedCapAt ist.state.slotCapAt ist.state.getUntyped? r u →
        SystemState.untypedCapAt ist.state.slotCapAt ist.state.getUntyped? r' u → r = r') ∧
      ∀ u U, ist.state.getUntyped? u = some U → U.children = []) :
    (∀ u r r', SystemState.untypedCapAt ist'.state.slotCapAt ist'.state.getUntyped? r u →
        SystemState.untypedCapAt ist'.state.slotCapAt ist'.state.getUntyped? r' u → r = r') ∧
      ∀ u U, ist'.state.getUntyped? u = some U → U.children = [] :=
  startInitialThreads_induct
    (fun i => (∀ u r r', SystemState.untypedCapAt i.state.slotCapAt i.state.getUntyped? r u →
        SystemState.untypedCapAt i.state.slotCapAt i.state.getUntyped? r' u → r = r') ∧
      ∀ u U, i.state.getUntyped? u = some U → U.children = [])
    (fun i tid _ hP => by
      have hInv := i.hAllTables.objects.1
      show (∀ u r r', SystemState.untypedCapAt (startInitialThreadOnCore i.state tid).slotCapAt
          (startInitialThreadOnCore i.state tid).getUntyped? r u →
          SystemState.untypedCapAt (startInitialThreadOnCore i.state tid).slotCapAt
          (startInitialThreadOnCore i.state tid).getUntyped? r' u → r = r') ∧
        ∀ u U, (startInitialThreadOnCore i.state tid).getUntyped? u = some U → U.children = []
      rw [startInitialThreadOnCore_getUntyped? i.state tid hInv]
      have hBack : ∀ {r u}, SystemState.untypedCapAt (startInitialThreadOnCore i.state tid).slotCapAt
          i.state.getUntyped? r u → SystemState.untypedCapAt i.state.slotCapAt i.state.getUntyped? r u :=
        fun {r _} ⟨c, hc, ht, hu⟩ => ⟨c, (startInitialThreadOnCore_slotCapAt_of_ne_none i.state tid
          hInv r (by rw [hc]; exact Option.some_ne_none _)).symm.trans hc, ht, hu⟩
      exact ⟨fun u r r' hr hr' => hP.1 u r r' (hBack hr) (hBack hr'), hP.2⟩)
    L ist ist' h hL

/-- **WS-ZA ZA5.4 part 20**: the starts keep every capability naming an untyped
an untyped capability: they write no capability slot and no untyped. -/
theorem startInitialThreads_untypedNamed (L : List SeLe4n.ThreadId)
    (ist ist' : IntermediateState) (h : startInitialThreads L ist = .ok ist')
    (hL : ∀ r u, SystemState.namesAt ist.state.slotCapAt r u → ist.state.getUntyped? u ≠ none →
      SystemState.untypedCapAt ist.state.slotCapAt ist.state.getUntyped? r u) :
    ∀ r u, SystemState.namesAt ist'.state.slotCapAt r u → ist'.state.getUntyped? u ≠ none →
      SystemState.untypedCapAt ist'.state.slotCapAt ist'.state.getUntyped? r u :=
  startInitialThreads_induct
    (fun i => ∀ r u, SystemState.namesAt i.state.slotCapAt r u → i.state.getUntyped? u ≠ none →
      SystemState.untypedCapAt i.state.slotCapAt i.state.getUntyped? r u)
    (fun i tid _ hP => by
      have hInv := i.hAllTables.objects.1
      show ∀ r u, SystemState.namesAt (startInitialThreadOnCore i.state tid).slotCapAt r u →
          (startInitialThreadOnCore i.state tid).getUntyped? u ≠ none →
          SystemState.untypedCapAt (startInitialThreadOnCore i.state tid).slotCapAt
            (startInitialThreadOnCore i.state tid).getUntyped? r u
      rw [startInitialThreadOnCore_getUntyped? i.state tid hInv]
      intro r u hr hu
      have hEq := startInitialThreadOnCore_slotCapAt_of_ne_none i.state tid hInv r
        (SystemState.namesAt_occupied hr)
      obtain ⟨c, hc, ht, hu'⟩ := hP r u ((SystemState.namesAt_of_eq hEq).mp hr) hu
      exact ⟨c, hEq.trans hc, ht, hu'⟩)
    L ist ist' h hL

/-- **WS-ZA ZA5.4**: the checked, idle-storing boot lists every slot holding a
capability among the configuration's boot capability slots: each such slot is
a configured object's (`bootFromPlatformCheckedWithIdleThreadsFor_ok_capObject_of_config`). -/
theorem bootFromPlatformCheckedWithIdleThreadsFor_bootSlotsListed
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformCheckedWithIdleThreadsFor cores config = .ok ist) :
    bootSlotsListed (bootCapabilitySlots config.initialObjects) ist.state := by
  intro r hr
  rw [SystemState.slotCapAt_eq_bind] at hr
  cases hO : ist.state.objects[r.cnode]? with
  | none => rw [hO] at hr; exact absurd rfl hr
  | some o =>
    rw [hO, Option.bind_some] at hr
    obtain ⟨e, he, hId, hObj⟩ :=
      bootFromPlatformCheckedWithIdleThreadsFor_ok_capObject_of_config cores config ist h
        r.cnode o hO r.slot hr
    have hm := mem_bootCapabilitySlots he (s := r.slot) (by rw [hObj]; exact hr)
    rw [hId] at hm
    exact hm

/-- **WS-ZA ZA5.4**: the starts keep every capability slot listed. -/
theorem startInitialThreads_bootSlotsListed (rs : List SlotRef) (L : List SeLe4n.ThreadId)
    (ist ist' : IntermediateState) (h : startInitialThreads L ist = .ok ist')
    (hL : bootSlotsListed rs ist.state) : bootSlotsListed rs ist'.state :=
  startInitialThreads_induct (fun i => bootSlotsListed rs i.state)
    (fun i tid _ hP r hr => hP r
      (startInitialThreadOnCore_slotCapAt_ne_none i.state tid i.hAllTables.objects.1 r hr))
    L ist ist' h hL

/-- **WS-BP BP7.11**: the started stage leaves a state of linked boot shape:
the starts keep the boot shape, and the linking takes it to the linked one
(`linkBootCapabilities_bootLinkedShape`). -/
theorem bootFromPlatformCheckedStartedFor_bootLinkedShape
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (hNodup : cores.Nodup)
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor cores config = .ok ist) :
    bootLinkedShape ist := by
  obtain ⟨base, started, hBase, hStart, rfl⟩ := bootFromPlatformCheckedStartedFor_ok cores config ist h
  have hSole := startInitialThreads_untypedsSole _ _ _ hStart
    ⟨bootFromPlatformCheckedWithIdleThreadsFor_ok_untypedCapUnique cores config base hBase,
      bootFromPlatformCheckedWithIdleThreadsFor_ok_untypedsUncarved cores config base hBase⟩
  exact linkBootCapabilities_bootLinkedShape config started
    (startInitialThreads_induct bootStartShape
      (fun ist tid hs hP => startInitialThread_preserves_bootStartShape ist tid hs hP)
      _ _ _ hStart
      (bootFromPlatformCheckedWithIdleThreadsFor_bootStartShape cores hNodup config base hBase))
    (startInitialThreads_bootSlotsListed _ _ _ _ hStart
      (bootFromPlatformCheckedWithIdleThreadsFor_bootSlotsListed cores config base hBase))
    (startInitialThreads_capabilitiesLive _ _ _ hStart
      (bootFromPlatformCheckedWithIdleThreadsFor_ok_capabilitiesLive cores config base hBase))
    hSole.1 hSole.2
    (startInitialThreads_untypedNamed _ _ _ hStart
      (bootFromPlatformCheckedWithIdleThreadsFor_ok_untypedNamed cores config base hBase))

/-- **WS-BP BP7.11**: **the state the started boot installs satisfies the
proof-layer invariant bundle** — the idle boot's argument, applied to the state
after the starts and the linking, because the starts keep what it reads and the
linking leaves a sound tree. -/
theorem bootFromPlatformCheckedStartedFor_proofLayerInvariantBundle
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (hNodup : cores.Nodup)
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor cores config = .ok ist) :
    Architecture.proofLayerInvariantBundle ist.state :=
  proofLayerInvariantBundle_of_bootLinkedShape ist
    (bootFromPlatformCheckedStartedFor_bootLinkedShape cores hNodup config ist h)

/-- WS-ZA ZA6.8: **the state the started boot installs keeps no linked thread
current or resident** — the first entry's precondition for
`syscallDispatchEntryState_preserves_yieldLinkedNotResident` and its siblings. -/
theorem bootFromPlatformCheckedStartedFor_yieldLinkedNotResident
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (hNodup : cores.Nodup)
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor cores config = .ok ist) :
    ist.state.yieldLinkedNotResident :=
  yieldLinkedNotResident_of_bootLinkedShape ist
    (bootFromPlatformCheckedStartedFor_bootLinkedShape cores hNodup config ist h)

/-- WS-ZA ZA5.4 part 36: **the state the started boot installs satisfies the
untyped memory invariant.**  Every capability is a configured one at free index
0 (`bootFromPlatformCheckedWithIdleThreadsFor_ok_freeIndexZero`), no untyped
records a child and none is named from two slots
(`bootFromPlatformCheckedWithIdleThreadsFor_ok_untypedsUncarved`,
`…_ok_untypedCapUnique`); the starts write no capability slot and no untyped,
and the linking writes derivation links and the tree alone. -/
theorem bootFromPlatformCheckedStartedFor_untypedMemoryInvariant
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformCheckedStartedFor cores config = .ok ist) :
    untypedMemoryInvariant ist.state := by
  obtain ⟨base, started, hBase, hStart, rfl⟩ := bootFromPlatformCheckedStartedFor_ok cores config ist h
  have hSole := startInitialThreads_untypedsSole _ _ _ hStart
    ⟨bootFromPlatformCheckedWithIdleThreadsFor_ok_untypedCapUnique cores config base hBase,
      bootFromPlatformCheckedWithIdleThreadsFor_ok_untypedsUncarved cores config base hBase⟩
  have hIdx : ∀ r c, started.state.slotCapAt r = some c → c.freeIndex = 0 :=
    startInitialThreads_induct (fun i => ∀ r c, i.state.slotCapAt r = some c → c.freeIndex = 0)
      (fun i tid _ hP r c hc => by
        have hc' : (startInitialThreadOnCore i.state tid).slotCapAt r = some c := hc
        exact hP r c ((startInitialThreadOnCore_slotCapAt_of_ne_none i.state tid i.hAllTables.objects.1 r
          (by rw [hc']; exact Option.some_ne_none _)).symm.trans hc'))
      _ _ _ hStart (bootFromPlatformCheckedWithIdleThreadsFor_ok_freeIndexZero cores config base hBase)
  have hA := linkBootCapabilities_agree config started
  have hUt : (linkBootCapabilities config started).state.getUntyped? = started.state.getUntyped? :=
    hA.getUntyped?
  have hBack : ∀ {r u}, SystemState.untypedCapAt (linkBootCapabilities config started).state.slotCapAt
      (linkBootCapabilities config started).state.getUntyped? r u →
      SystemState.untypedCapAt started.state.slotCapAt started.state.getUntyped? r u :=
    fun {r _} ⟨c, hc, ht, hu⟩ => ⟨c, (hA.slotCapAt r).symm.trans hc, ht, hUt ▸ hu⟩
  exact untypedMemoryInvariant_of_pristine
    (fun r c hc => hIdx r c ((hA.slotCapAt r).symm.trans hc))
    (fun u U hU => hSole.2 u U (hUt ▸ hU))
    (fun u r r' hr hr' => hSole.1 u r r' (hBack hr) (hBack hr'))

/-- **WS-BP BP7.11**: the end-to-end bridge for the started boot — the bundle of
the state it installs, and the frozen bundle of its freeze. -/
theorem bootToRuntime_invariantBridge_started
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (hNodup : cores.Nodup)
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor cores config = .ok ist) :
    Architecture.proofLayerInvariantBundle ist.state ∧
    SeLe4n.Model.apiInvariantBundle_frozen (SeLe4n.Model.freeze ist) :=
  let hBundle :=
    bootFromPlatformCheckedStartedFor_proofLayerInvariantBundle cores hNodup config ist h
  ⟨hBundle, SeLe4n.Model.freeze_preserves_invariants _ hBundle⟩

/-- **WS-BP BP7.11**: the started boot dispatches nothing — every core's current
slot is still `none`, so each core's first scheduling point is what selects. -/
theorem bootFromPlatformCheckedStartedFor_currentOnCore
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (hNodup : cores.Nodup)
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor cores config = .ok ist)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    ist.state.scheduler.currentOnCore c = none := by
  obtain ⟨_, _, _, _, ⟨rq, re, rp, hSch⟩, _⟩ :=
    bootFromPlatformCheckedStartedFor_bootLinkedShape cores hNodup config ist h
  rw [hSch]
  exact (default_state_perCoreInitialized c).1

-- ============================================================================
-- §4  The classification, the started threads, and what the stage frames
-- ============================================================================

/-- **WS-BP BP7.11**: **every named thread is started** — queued on some core
and stored `.Ready` — on the state a successful stage leaves.  Each start
starts its own thread (`Kernel.startInitialThreadOnCore_threadStarted`) and
leaves every earlier one started
(`Kernel.startInitialThreadOnCore_preserves_threadStarted`). -/
theorem startInitialThreads_ok_started :
    ∀ (L : List SeLe4n.ThreadId) (ist ist' : IntermediateState),
      ist.state.runQueueRefined →
      startInitialThreads L ist = .ok ist' → ∀ tid ∈ L, threadStarted ist'.state tid := by
  intro L
  induction L with
  | nil => intro _ _ _ _ tid hMem; cases hMem
  | cons tid rest ih =>
    intro ist ist' hR h tid' hMem
    unfold startInitialThreads at h
    split at h
    · rename_i hStart
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact startInitialThreads_induct (fun i => threadStarted i.state tid')
          (fun i t hs hP => startInitialThreadOnCore_preserves_threadStarted hs i.hAllTables.objects.1 hP)
          rest _ _ h (startInitialThreadOnCore_threadStarted hStart ist.hAllTables.objects.1 hR)
      · exact ih _ _ (startInitialThreadOnCore_runQueueRefined _ _ ist.hAllTables.objects.1 hR) h tid' hRest
    · cases h

/-- **WS-BP BP7.11**: ...on the started boot, every thread the configuration
names. -/
theorem bootFromPlatformCheckedStartedFor_started
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor cores config = .ok ist) :
    ∀ tid ∈ config.initialThreads, threadStarted ist.state tid := by
  obtain ⟨base, started, hBase, hStart, rfl⟩ := bootFromPlatformCheckedStartedFor_ok cores config ist h
  obtain ⟨_, _, _, _, _, hRun, _⟩ := bootFromPlatformCheckedWithIdleThreadsFor_bootStartShape cores
    (bootFromPlatformCheckedWithIdleThreadsFor_ok_nodup cores config base hBase) config base hBase
  exact fun tid hT => threadStarted_of_agree (linkBootCapabilities_agree config started)
    (startInitialThreads_ok_started _ _ _ hRun hStart tid hT)

/-- **WS-BP BP7.11**: **the started boot keeps the full thread-state
classification** — the idle boot's (`bootFromPlatformCheckedWithIdleThreads_threadStateConsistent`)
carried across every start, which stores a started thread `.Ready` exactly as
it queues it. -/
theorem bootFromPlatformCheckedStartedFor_allCores_threadStateConsistent
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor SeLe4n.Kernel.Concurrency.allCores config = .ok ist) :
    threadStateConsistent ist.state := by
  obtain ⟨base, started, hBase, hStart, rfl⟩ := bootFromPlatformCheckedStartedFor_ok _ config ist h
  obtain ⟨_, _, _, _, _, hRun, _⟩ := bootFromPlatformCheckedWithIdleThreadsFor_bootStartShape _
    SeLe4n.Kernel.Concurrency.allCores_nodup config base hBase
  rw [bootFromPlatformCheckedWithIdleThreadsFor_allCores] at hBase
  refine threadStateConsistent_of_agree (linkBootCapabilities_agree config started)
    (linkBootCapabilities_scheduler config started) ?_
  exact (startInitialThreads_induct (fun i => i.state.runQueueRefined ∧ threadStateConsistent i.state)
    (fun i t hs hP => ⟨startInitialThreadOnCore_runQueueRefined _ _ i.hAllTables.objects.1 hP.1,
      startInitialThreadOnCore_preserves_threadStateConsistent hs i.hAllTables.objects.1 hP.1 hP.2⟩)
    _ _ _ hStart ⟨hRun, bootFromPlatformCheckedWithIdleThreads_threadStateConsistent config base hBase⟩).2

/-- **WS-BP BP7.11**: ...and with it the inactive-flag relation the live
decisions read. -/
theorem bootFromPlatformCheckedStartedFor_allCores_threadInactiveFlagConsistent
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor SeLe4n.Kernel.Concurrency.allCores config = .ok ist) :
    threadInactiveFlagConsistent ist.state :=
  threadStateConsistent_implies_threadInactiveFlagConsistent _
    (bootFromPlatformCheckedStartedFor_allCores_threadStateConsistent config ist h)

/-- **The start of a startable thread is a run-queue stage**: the `.Ready` mark
leaves its run links alone and suspends nothing, and the wake that follows
queues a thread no core runs, now active. -/
theorem startInitialThreadOnCore_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (hs : initialThreadStartable st tid = true) :
    SystemState.RunQueueStage st (startInitialThreadOnCore st tid) :=
  SystemState.RunQueueStage.of_invExt fun hInv => by
    obtain ⟨tcb, hT, -, -, -, -, hRun⟩ := initialThreadStartable_spec hs
    unfold startInitialThreadOnCore
    refine (SystemState.RunQueueStage.updateTcb st tid (f := fun t => { t with threadState := .Ready })
      (fun _ _ => rfl)).trans (enqueueRunnableOnCore_runQueueStage _ _ tid ?_ ?_
        (fun x hx => by
          rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv, hT] at hx
          cases hx; exact homedOn_determineTargetCore st tid tcb hT))
    · have h0 : st.currentNowhere tid := fun c hc => by
        simp only [runningOnSomeCore, SeLe4n.Kernel.Concurrency.allCores,
          List.any_eq_false] at hRun
        exact hRun c (List.mem_finRange c) (by simp [hc])
      exact SystemState.currentNowhere.of_scheduler_eq
        (by rw [SystemState.updateTcb_scheduler]) h0
    · refine ⟨{ tcb with threadState := .Ready }, ?_, by simp [TCB.Active]⟩
      rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv, hT]; rfl

/-- **The started boot keeps every current thread off the run queues** — the
idle boot's `currentDequeuedUnique`
(`bootFromPlatformCheckedWithIdleThreads_currentDequeuedUnique`) carried across
every start, each a run-queue stage. -/
theorem bootFromPlatformCheckedStartedFor_allCores_currentDequeuedUnique
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor SeLe4n.Kernel.Concurrency.allCores config = .ok ist) :
    ist.state.runQueueRefined ∧ ist.state.currentDequeuedUnique := by
  obtain ⟨base, started, hBase, hStart, rfl⟩ := bootFromPlatformCheckedStartedFor_ok _ config ist h
  obtain ⟨_, _, _, _, _, hRun, _⟩ := bootFromPlatformCheckedWithIdleThreadsFor_bootStartShape _
    SeLe4n.Kernel.Concurrency.allCores_nodup config base hBase
  rw [bootFromPlatformCheckedWithIdleThreadsFor_allCores] at hBase
  have hA := linkBootCapabilities_agree config started
  have hSch := linkBootCapabilities_scheduler config started
  suffices hP : started.state.runQueueRefined ∧ started.state.currentDequeuedUnique from
    ⟨SystemState.runQueueRefined_of_frame (runLinkOn_of_agree hA) (by rw [hSch])
      (by rw [hSch]) hP.1,
     SystemState.currentDequeuedUniqueExcept_of_eq (by rw [hSch]) (runLinkOn_of_agree hA)
      (stateMono_of_agree hA) hP.2⟩
  exact startInitialThreads_induct
    (fun i => i.state.runQueueRefined ∧ i.state.currentDequeuedUnique)
    (fun i t hs hP => by
      have hS := (startInitialThreadOnCore_runQueueStage _ _ hs).entry
      have hR' := (hS.1 i.hAllTables.objects.1 hP.1).2
      exact ⟨hR', hS.2 i.hAllTables.objects.1 hP.1 hR' hP.2⟩)
    _ _ _ hStart
    ⟨hRun, bootFromPlatformCheckedWithIdleThreads_currentDequeuedUnique config base hBase⟩

/-- **WS-BP BP7.11** (frame): the starts write the object store and the
scheduler, and nothing else — the machine the boot configured is the machine it
installs. -/
theorem startInitialThreads_machine :
    ∀ (L : List SeLe4n.ThreadId) (ist ist' : IntermediateState),
      startInitialThreads L ist = .ok ist' → ist'.state.machine = ist.state.machine := by
  intro L ist ist' h
  exact startInitialThreads_induct (fun i => i.state.machine = ist.state.machine)
    (fun i t _ hP => by
      show (startInitialThreadOnCore i.state t).machine = _
      rw [startInitialThreadOnCore_frame i.state t]; exact hP)
    L ist ist' h rfl

/-- **WS-BP BP7.11** (frame): every object that is not a TCB is where the idle
boot put it. -/
theorem startInitialThreads_objects_of_nonTcb (L : List SeLe4n.ThreadId)
    (ist ist' : IntermediateState) (h : startInitialThreads L ist = .ok ist')
    (k : SeLe4n.ObjId) (obj : KernelObject) (hNot : ∀ t, obj ≠ .tcb t)
    (hObj : ist.state.objects[k]? = some obj) :
    ist'.state.objects[k]? = some obj :=
  startInitialThreads_induct (fun i => i.state.objects[k]? = some obj)
    (fun i _ _ hP => startInitialThreadOnCore_objects_of_nonTcb _ _ i.hAllTables.objects.1 _ _ hNot hP)
    L ist ist' h hObj

/-- **WS-BP BP7.11** (frame): every thread that resolved still resolves. -/
theorem startInitialThreads_getTcb?_isSome (L : List SeLe4n.ThreadId)
    (ist ist' : IntermediateState) (h : startInitialThreads L ist = .ok ist')
    (t : SeLe4n.ThreadId) (hT : (ist.state.getTcb? t).isSome = true) :
    (ist'.state.getTcb? t).isSome = true :=
  startInitialThreads_induct (fun i => (i.state.getTcb? t).isSome = true)
    (fun i _ _ hP => startInitialThreadOnCore_getTcb?_isSome _ _ _ i.hAllTables.objects.1 hP)
    L ist ist' h hT

/-- **WS-BP BP7.11**: the labeling's declared witnesses, installed on the idle
boot, are installed on the started one. -/
theorem startInitialThreads_preserves_declaredWitnessesInstalled (L : List SeLe4n.ThreadId)
    (ist ist' : IntermediateState) (h : startInitialThreads L ist = .ok ist')
    (ctx : LabelingContext) (hW : declaredWitnessesInstalled ist.state ctx = true) :
    declaredWitnessesInstalled ist'.state ctx = true := by
  unfold declaredWitnessesInstalled at hW ⊢
  cases hSep : ctx.separatedThreads with
  | none => rw [hSep] at hW; exact hW
  | some p =>
    rw [hSep] at hW
    simp only [Bool.and_eq_true] at hW ⊢
    exact ⟨startInitialThreads_getTcb?_isSome L ist ist' h _ hW.1,
      startInitialThreads_getTcb?_isSome L ist ist' h _ hW.2⟩

/-- **WS-BP BP7.11**: a list of distinct threads, each startable on the state
the stage begins from, is started in full — the stage is the fold of the start,
with no refusal. -/
theorem startInitialThreads_eq_foldl :
    ∀ (L : List SeLe4n.ThreadId) (ist : IntermediateState), L.Nodup →
      (∀ tid ∈ L, initialThreadStartable ist.state tid = true) →
      startInitialThreads L ist = .ok (L.foldl startInitialThread ist) := by
  intro L
  induction L with
  | nil => intro _ _ _; rfl
  | cons tid rest ih =>
    intro ist hNodup hAll
    have hHead := hAll tid (List.mem_cons_self ..)
    unfold startInitialThreads
    rw [if_pos hHead, List.foldl_cons]
    apply ih _ (List.nodup_cons.mp hNodup).2
    intro tid' hMem
    have hNe : tid' ≠ tid := fun hEq => (List.nodup_cons.mp hNodup).1 (hEq ▸ hMem)
    exact initialThreadStartable_of_start_ne hNe ist.hAllTables.objects.1
      (hAll tid' (List.mem_cons_of_mem _ hMem))

/-- **WS-BP BP7.11**: **on the all-cores idle boot, a configured thread is
startable** exactly when its own record allows it — a positive time slice and no
inherited boost.  Everything else is the boot's: the thread resolves, it is on no
queue (the idle boot queues nothing) and on no current slot, and the idle boot's classification makes it
`.Inactive` because it is unplaced and `.ready`. -/
theorem bootFromPlatformCheckedWithIdleThreads_initialThreadStartable
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedWithIdleThreads config = .ok ist)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hT : ist.state.getTcb? tid = some tcb)
    (hNotIdle : ∀ c, tid ≠ idleThreadId c)
    (hSlice : 0 < tcb.timeSlice) (hBoost : tcb.pipBoost = none) :
    initialThreadStartable ist.state tid = true := by
  have hRun : runningOnSomeCore ist.state tid = false := by
    unfold runningOnSomeCore
    rw [List.any_eq_false]
    intro c _
    rw [bootFromPlatformCheckedWithIdleThreads_currentAllNone config ist h c]
    simp
  have hQ : runnableOnSomeCore ist.state tid = false := by
    unfold runnableOnSomeCore
    rw [List.any_eq_false]
    intro c _ hMem
    rw [(bootFromPlatformCheckedWithIdleThreads_runQueueRefined config ist h c).queuedOn] at hMem
    exact bootFromPlatformCheckedWithIdleThreads_not_mem_runQueueOnCore config ist h c tid
      ((SeLe4n.Kernel.RunQueue.mem_toList_iff_mem _ _).mpr hMem)
  have hI : isIdleThreadId tid = false := by
    cases hI : isIdleThreadId tid
    · rfl
    · obtain ⟨c, hc⟩ := (isIdleThreadId_iff tid).mp hI
      exact absurd hc (hNotIdle c)
  have hObj := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
  have hCons := bootFromPlatformCheckedWithIdleThreads_threadStateConsistent config ist h _ _ hObj
  rw [← bootFromPlatformCheckedWithIdleThreadsFor_allCores] at h
  have hIpc := (bootFromPlatformCheckedWithIdleThreadsFor_ok_tcb_quiescent _ config ist h _ _ hObj).1
  have hInactive : tcb.threadState = .Inactive := by
    rw [hCons]
    unfold inferThreadState threadRunningOnSomeCore threadQueuedOnSomeCore
    have hEta : (⟨tid.toObjId.toNat⟩ : SeLe4n.ThreadId) = tid := rfl
    rw [hEta, hRun, hQ, hI, hIpc]
    rfl
  unfold initialThreadStartable
  rw [hT, hRun, hQ, hI]
  simp [hInactive, hBoost, hSlice]

end SeLe4n.Platform.Boot
