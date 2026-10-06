-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.Boot

/-!
# WS-BP BP7.11 — the boot starts its designated threads

The checked, idle-enqueued boot (`bootFromPlatformCheckedWithIdleThreadsFor`)
installs every configured thread `.Inactive` and queues nothing but each
declared core's idle thread, so until this stage no deployment thread ever ran:
nothing held a capability to either initial thread's TCB outside that thread's
own CSpace, and nothing resumed it.  This module is the stage after the idle
enqueue that **starts** the threads a configuration names
(`PlatformConfig.initialThreads`) — each through the kernel model's own start
(`Kernel.startInitialThreadOnCore`), so it is `.Ready` and queued on its home
core, and each core's first scheduling point dispatches it ahead of idle by
priority.  A platform binding names the threads its hardware boot starts
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
operation's own preservation theorems (the shape `enqueueIdleThread` takes). -/
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
idle-enqueued boot, then the configuration's named threads started. -/
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
  obtain ⟨hShape, hFields, hAsid, hUntyped, ⟨rq, rp, hSch⟩, hQueue⟩ := h
  have hFrame := startInitialThreadOnCore_frame ist.state tid hInv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro oid obj hObj
    rcases startInitialThreadOnCore_objects_cases ist.state tid hInv oid obj hObj with
      hB | ⟨t, hT, rfl | rfl⟩
    · exact hShape oid obj hB
    all_goals
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hShape oid _ hT
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro x hx <;> cases hx
      obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := h4 t rfl
      exact ⟨t1, by first | exact t2 | rfl, t3, t4, t5, t6, t7, t8, t9⟩
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
        hB | ⟨_, _, hc | hc⟩
      · rw [hFrame]; exact hA2 oid root hB
      all_goals cases hc
  · show Kernel.untypedRegionsDisjoint (startInitialThreadOnCore ist.state tid)
    refine untypedRegionsDisjoint_of_untyped_subset hUntyped ?_
    intro oid ut hObj
    rcases startInitialThreadOnCore_objects_cases ist.state tid hInv oid _ hObj with
      hB | ⟨_, _, hc | hc⟩
    · exact hB
    all_goals cases hc
  · obtain ⟨rq', rp', hrq'⟩ := startInitialThreadOnCore_scheduler_runQueueOnly ist.state tid
    refine ⟨rq', rp', ?_⟩
    show (startInitialThreadOnCore ist.state tid).scheduler = _
    rw [hrq', hSch]
  · exact startInitialThreadOnCore_preserves_runQueueBootSound hStart hInv bootCoreId hQueue

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
  obtain ⟨_, _, _, _, ⟨rq, rp, hSch⟩, _⟩ :=
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
      startInitialThreads L ist = .ok ist' → ∀ tid ∈ L, threadStarted ist'.state tid := by
  intro L
  induction L with
  | nil => intro _ _ _ tid hMem; cases hMem
  | cons tid rest ih =>
    intro ist ist' h tid' hMem
    unfold startInitialThreads at h
    split at h
    · rename_i hStart
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact startInitialThreads_induct (fun i => threadStarted i.state tid')
          (fun i t hs hP => startInitialThreadOnCore_preserves_threadStarted hs i.hAllTables.1.1 hP)
          rest _ _ h (startInitialThreadOnCore_threadStarted hStart ist.hAllTables.1.1)
      · exact ih _ _ h tid' hRest
    · cases h

/-- **WS-BP BP7.11**: ...on the started boot, every thread the configuration
names. -/
theorem bootFromPlatformCheckedStartedFor_started
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor cores config = .ok ist) :
    ∀ tid ∈ config.initialThreads, threadStarted ist.state tid := by
  obtain ⟨base, _, hStart⟩ := bootFromPlatformCheckedStartedFor_ok cores config ist h
  exact startInitialThreads_ok_started _ _ _ hStart

/-- **WS-BP BP7.11**: **the started boot keeps the full thread-state
classification** — the idle boot's (`bootFromPlatformCheckedWithIdleThreads_threadStateConsistent`)
carried across every start, which stores a started thread `.Ready` exactly as
it queues it. -/
theorem bootFromPlatformCheckedStartedFor_allCores_threadStateConsistent
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor SeLe4n.Kernel.Concurrency.allCores config = .ok ist) :
    threadStateConsistent ist.state := by
  obtain ⟨base, hBase, hStart⟩ := bootFromPlatformCheckedStartedFor_ok _ config ist h
  rw [bootFromPlatformCheckedWithIdleThreadsFor_allCores] at hBase
  exact startInitialThreads_induct (fun i => threadStateConsistent i.state)
    (fun i t hs hP => startInitialThreadOnCore_preserves_threadStateConsistent hs i.hAllTables.1.1 hP)
    _ _ _ hStart (bootFromPlatformCheckedWithIdleThreads_threadStateConsistent config base hBase)

/-- **WS-BP BP7.11**: ...and with it the inactive-flag relation the live
decisions read. -/
theorem bootFromPlatformCheckedStartedFor_allCores_threadInactiveFlagConsistent
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedStartedFor SeLe4n.Kernel.Concurrency.allCores config = .ok ist) :
    threadInactiveFlagConsistent ist.state :=
  threadStateConsistent_implies_threadInactiveFlagConsistent _
    (bootFromPlatformCheckedStartedFor_allCores_threadStateConsistent config ist h)

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
      rw [startInitialThreadOnCore_frame i.state t i.hAllTables.1.1]; exact hP)
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
queue (the idle boot queues only idle threads, and a configured thread is not
one) and on no current slot, and the idle boot's classification makes it
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
    have hIn := (SeLe4n.Kernel.RunQueue.mem_toList_iff_mem _ _).mpr hMem
    rw [bootFromPlatformCheckedWithIdleThreads_mem_runQueueOnCore_iff config ist h c] at hIn
    exact hNotIdle c hIn
  have hObj := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
  have hCons := bootFromPlatformCheckedWithIdleThreads_threadStateConsistent config ist h _ _ hObj
  rw [← bootFromPlatformCheckedWithIdleThreadsFor_allCores] at h
  have hIpc := (bootFromPlatformCheckedWithIdleThreadsFor_ok_tcb_quiescent _ config ist h _ _ hObj).1
  have hInactive : tcb.threadState = .Inactive := by
    rw [hCons]
    unfold inferThreadState threadRunningOnSomeCore threadQueuedOnSomeCore
    have hEta : (⟨tid.toObjId.toNat⟩ : SeLe4n.ThreadId) = tid := rfl
    rw [hEta, hRun, hQ, hIpc]
    rfl
  unfold initialThreadStartable
  rw [hT, hRun, hQ]
  simp [hInactive, hBoost, hSlice]

end SeLe4n.Platform.Boot
