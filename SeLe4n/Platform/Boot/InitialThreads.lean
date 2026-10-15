-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.Boot
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
    ist.hAllTables.1.1 ist.hPerObjectSlots
  hPerObjectMappings := startInitialThreadOnCore_preserves_perObjectMappingsInvariant ist.state tid
    ist.hAllTables.1.1 ist.hPerObjectMappings
  hLifecycleConsistent := startInitialThreadOnCore_preserves_objectTypeMetadataConsistent
    ist.state tid ist.hAllTables.1.1 ist.hLifecycleConsistent

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
idle-storing boot, then the configuration's named threads started. -/
def bootFromPlatformCheckedStartedFor
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig) :
    Except String IntermediateState :=
  (bootFromPlatformCheckedWithIdleThreadsFor cores config).bind
    (startInitialThreads config.initialThreads)

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

/-- **WS-BP BP7.11**: with no named thread the stage is the idle boot — every
theorem about the idle boot is a theorem about the started boot of a
configuration that names none. -/
theorem bootFromPlatformCheckedStartedFor_of_nil
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (h : config.initialThreads = []) :
    bootFromPlatformCheckedStartedFor cores config =
      bootFromPlatformCheckedWithIdleThreadsFor cores config := by
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

/-- **WS-BP BP7.11**: after a successful idle boot, the stage is the starts —
stated over variables, so a concrete configuration rewrites with it instead of
unfolding the bind against its own boot state. -/
theorem bootFromPlatformCheckedStartedFor_of_idle
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (base : IntermediateState)
    (h : bootFromPlatformCheckedWithIdleThreadsFor cores config = .ok base) :
    bootFromPlatformCheckedStartedFor cores config =
      startInitialThreads config.initialThreads base := by
  unfold bootFromPlatformCheckedStartedFor
  rw [h]
  rfl

/-- **WS-BP BP7.11**: a successful stage is a successful idle boot followed by a
successful start of every named thread. -/
theorem bootFromPlatformCheckedStartedFor_ok
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor cores config = .ok ist) :
    ∃ base, bootFromPlatformCheckedWithIdleThreadsFor cores config = .ok base ∧
      startInitialThreads config.initialThreads base = .ok ist := by
  unfold bootFromPlatformCheckedStartedFor at h
  cases hB : bootFromPlatformCheckedWithIdleThreadsFor cores config with
  | error e => rw [hB] at h; cases h
  | ok base => rw [hB] at h; exact ⟨base, rfl, h⟩

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

/-- **WS-BP BP7.11**: **a start keeps the boot shape.**  The written TCB was
boot-shaped and the start moves only its flag and its IPC state to `.ready`;
nothing else in the object store moves, so the ASID table, the untypeds and
the quiescent fields are as they were; the scheduler gains one run-queue
member; and the boot core's queue stays boot-sound
(`Kernel.startInitialThreadOnCore_preserves_runQueueBootSound`). -/
theorem startInitialThread_preserves_bootStartShape (ist : IntermediateState)
    (tid : SeLe4n.ThreadId) (hStart : initialThreadStartable ist.state tid = true)
    (h : bootStartShape ist) : bootStartShape (startInitialThread ist tid) := by
  have hInv := ist.hAllTables.1.1
  obtain ⟨hShape, hFields, hAsid, hUntyped, ⟨rq, re, rp, hSch⟩, hRun, hQueue⟩ := h
  have hFrame := startInitialThreadOnCore_frame ist.state tid
  refine ⟨?_, ?_, ?_, ?_, ?_, startInitialThreadOnCore_runQueueRefined ist.state tid hInv hRun, ?_⟩
  · intro oid obj hObj
    rcases startInitialThreadOnCore_objects_cases ist.state tid hInv oid obj hObj with
      hB | ⟨t, t', hT, rfl, he⟩
    · exact hShape oid obj hB
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hShape oid _ hT
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro x hx <;> cases hx
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
      have r4 : t'.replyWaitersCount = 0 := c4.trans t15
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
        (TCB.proj_eq_of_withoutRunLinks_eq TCB.ntfnNext he).trans t11, r1, r2, r3, r4⟩
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

/-- **WS-BP BP7.11**: the started stage leaves a state of boot shape. -/
theorem bootFromPlatformCheckedStartedFor_bootStartShape
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (hNodup : cores.Nodup)
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor cores config = .ok ist) :
    bootStartShape ist := by
  obtain ⟨base, hBase, hStart⟩ := bootFromPlatformCheckedStartedFor_ok cores config ist h
  exact startInitialThreads_induct bootStartShape
    (fun ist tid hs hP => startInitialThread_preserves_bootStartShape ist tid hs hP)
    _ _ _ hStart
    (bootFromPlatformCheckedWithIdleThreadsFor_bootStartShape cores hNodup config base hBase)

/-- **WS-BP BP7.11**: **the state the started boot installs satisfies the
proof-layer invariant bundle** — the idle boot's argument, applied to the state
after the starts, because the starts keep what it reads. -/
theorem bootFromPlatformCheckedStartedFor_proofLayerInvariantBundle
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (hNodup : cores.Nodup)
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor cores config = .ok ist) :
    Architecture.proofLayerInvariantBundle ist.state :=
  proofLayerInvariantBundle_of_bootStartShape ist
    (bootFromPlatformCheckedStartedFor_bootStartShape cores hNodup config ist h)

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
    bootFromPlatformCheckedStartedFor_bootStartShape cores hNodup config ist h
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
          (fun i t hs hP => startInitialThreadOnCore_preserves_threadStarted hs i.hAllTables.1.1 hP)
          rest _ _ h (startInitialThreadOnCore_threadStarted hStart ist.hAllTables.1.1 hR)
      · exact ih _ _ (startInitialThreadOnCore_runQueueRefined _ _ ist.hAllTables.1.1 hR) h tid' hRest
    · cases h

/-- **WS-BP BP7.11**: ...on the started boot, every thread the configuration
names. -/
theorem bootFromPlatformCheckedStartedFor_started
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor cores config = .ok ist) :
    ∀ tid ∈ config.initialThreads, threadStarted ist.state tid := by
  obtain ⟨base, hBase, hStart⟩ := bootFromPlatformCheckedStartedFor_ok cores config ist h
  obtain ⟨_, _, _, _, _, hRun, _⟩ := bootFromPlatformCheckedWithIdleThreadsFor_bootStartShape cores
    (bootFromPlatformCheckedWithIdleThreadsFor_ok_nodup cores config base hBase) config base hBase
  exact startInitialThreads_ok_started _ _ _ hRun hStart

/-- **WS-BP BP7.11**: **the started boot keeps the full thread-state
classification** — the idle boot's (`bootFromPlatformCheckedWithIdleThreads_threadStateConsistent`)
carried across every start, which stores a started thread `.Ready` exactly as
it queues it. -/
theorem bootFromPlatformCheckedStartedFor_allCores_threadStateConsistent
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor SeLe4n.Kernel.Concurrency.allCores config = .ok ist) :
    threadStateConsistent ist.state := by
  obtain ⟨base, hBase, hStart⟩ := bootFromPlatformCheckedStartedFor_ok _ config ist h
  obtain ⟨_, _, _, _, _, hRun, _⟩ := bootFromPlatformCheckedWithIdleThreadsFor_bootStartShape _
    SeLe4n.Kernel.Concurrency.allCores_nodup config base hBase
  rw [bootFromPlatformCheckedWithIdleThreadsFor_allCores] at hBase
  exact (startInitialThreads_induct (fun i => i.state.runQueueRefined ∧ threadStateConsistent i.state)
    (fun i t hs hP => ⟨startInitialThreadOnCore_runQueueRefined _ _ i.hAllTables.1.1 hP.1,
      startInitialThreadOnCore_preserves_threadStateConsistent hs i.hAllTables.1.1 hP.1 hP.2⟩)
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
      (fun _ _ => rfl)).trans (enqueueRunnableOnCore_runQueueStage _ _ tid ?_ ?_)
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
  obtain ⟨base, hBase, hStart⟩ := bootFromPlatformCheckedStartedFor_ok _ config ist h
  obtain ⟨_, _, _, _, _, hRun, _⟩ := bootFromPlatformCheckedWithIdleThreadsFor_bootStartShape _
    SeLe4n.Kernel.Concurrency.allCores_nodup config base hBase
  rw [bootFromPlatformCheckedWithIdleThreadsFor_allCores] at hBase
  exact startInitialThreads_induct
    (fun i => i.state.runQueueRefined ∧ i.state.currentDequeuedUnique)
    (fun i t hs hP => by
      have hS := (startInitialThreadOnCore_runQueueStage _ _ hs).entry
      have hR' := (hS.1 i.hAllTables.1.1 hP.1).2
      exact ⟨hR', hS.2 i.hAllTables.1.1 hP.1 hR' hP.2⟩)
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
    (fun i _ _ hP => startInitialThreadOnCore_objects_of_nonTcb _ _ i.hAllTables.1.1 _ _ hNot hP)
    L ist ist' h hObj

/-- **WS-BP BP7.11** (frame): every thread that resolved still resolves. -/
theorem startInitialThreads_getTcb?_isSome (L : List SeLe4n.ThreadId)
    (ist ist' : IntermediateState) (h : startInitialThreads L ist = .ok ist')
    (t : SeLe4n.ThreadId) (hT : (ist.state.getTcb? t).isSome = true) :
    (ist'.state.getTcb? t).isSome = true :=
  startInitialThreads_induct (fun i => (i.state.getTcb? t).isSome = true)
    (fun i _ _ hP => startInitialThreadOnCore_getTcb?_isSome _ _ _ i.hAllTables.1.1 hP)
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
    exact initialThreadStartable_of_start_ne hNe ist.hAllTables.1.1
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
