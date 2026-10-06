-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.Selection

/-!
# The reschedule-SGI accumulator — the key-change hook and the flag-derived SGIs

The KSC-1 / HAL-3 row of `docs/REGISTERED_DEBT.md` (the accumulator slice;
WS-CB's `reschedulePendingOnCore` is the same flag, `HIERARCHICAL_CBS_PLAN.md`
§4.1 / §4.4).  `SchedulerState.reschedulePending` records, per core, that a
scheduling point is owed; `Model/State.lean` holds the field, its accessor and
the slot-level marks.  This module holds the two pieces that need the scheduler
operations:

* `markKeyChangeFor` — the one hook every writer of a thread's **effective
  key** (`resolveEffectivePrioDeadline`: `TCB.priority`, `TCB.pipBoost`,
  `TCB.schedContextBinding`, the bound context's deadline) calls after its
  write.  It is the single-thread instance of the commit diff's rules
  (`crossCoreSgiBody`, `PriorityInheritance/PerCore.lean`): a queued thread
  whose key changed flags its home core; a current thread whose effective
  priority dropped or whose effective deadline moved later flags the core
  running it; a raise, an unchanged key, or a thread placed nowhere flags
  nothing.  The writer hands in the key it read **before** the write, so the
  hook is exact at O(1) and never keeps the pre-state alive.

* `rescheduleSgisFromFlags` — the `.reschedule` SGIs a step owes, read off a
  captured pre-dispatch flag vector and the post-state's: one per remote core
  whose flag went `false → true`.  **Not yet the live decider**: in this slice
  the syscall commit still runs `computeCrossCoreSgis` (the whole-object-index
  diff), and the Tier 2 `reschedule_pending_suite` pins this list against the
  diff on every SMP scenario; the seam switch is the row's PR C and the
  set-equality theorem its PR B.

Slot writers (`enqueueRunnableOnCore`, `removeRunnableOnCore`,
`removeRunnableStepOnCore`, `migrateRunQueueOnAffinityChange`, the
SchedContext bind / unbind / yield placements) mark directly through
`SchedulerState.markReschedulePendingOnCore` — they already name the core they
write.  The flag is cleared only by the flagged core's own scheduling points,
`handleRescheduleSgiOnCore` and `scheduleEffectiveOnCore`, as their last write.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind allCores numCores)

/-- Mark every core of `cs` on which `p` holds — the key-change hook's write,
which flags each core whose queue or current slot holds the re-keyed thread
without assuming the thread sits on one core only. -/
def markReschedulePendingWhere (st : SystemState) (p : CoreId → Bool) :
    List CoreId → SystemState
  | [] => st
  | c :: cs => markReschedulePendingWhere
      (if p c then st.markReschedulePendingOnCore c else st) p cs

/-- Any projection the single mark leaves alone, the multi-core mark leaves
alone. -/
theorem markReschedulePendingWhere_extract_frame {F : Type} (extract : SystemState → F)
    (h : ∀ (s : SystemState) c, extract (s.markReschedulePendingOnCore c) = extract s)
    (st : SystemState) (p : CoreId → Bool) (cs : List CoreId) :
    extract (markReschedulePendingWhere st p cs) = extract st := by
  induction cs generalizing st with
  | nil => rfl
  | cons c cs ih =>
    simp only [markReschedulePendingWhere]
    rw [ih]
    split
    · exact h st c
    · rfl

/-- A core's flag after the multi-core mark: the old flag, or `p` on a listed
core. -/
theorem markReschedulePendingWhere_reschedulePendingOnCore (st : SystemState)
    (p : CoreId → Bool) (cs : List CoreId) (c' : CoreId) :
    (markReschedulePendingWhere st p cs).scheduler.reschedulePendingOnCore c' =
      (st.scheduler.reschedulePendingOnCore c' || (p c' && decide (c' ∈ cs))) := by
  induction cs generalizing st with
  | nil => simp [markReschedulePendingWhere]
  | cons c cs ih =>
    simp only [markReschedulePendingWhere]
    rw [ih]
    by_cases hc : c = c'
    · subst hc
      cases p c <;> simp [SystemState.markReschedulePendingOnCore]
    · split <;> simp [SystemState.markReschedulePendingOnCore, hc, List.mem_cons, Ne.symm hc]

/-- Flag every core whose scheduling decision a key write on `tid` has staled.
`preKey` is `resolveEffectivePrioDeadline` of `tid` read on the state before
the write; `st` is the state after it.  Mirrors `crossCoreSgiBody` for the one
thread: a core whose run queue holds `tid` is flagged when the key moved, and a
core whose current slot holds `tid` when its effective priority dropped or its
effective deadline moved later.  Every core is checked, so the hook assumes no
placement invariant (`markKeyChangeFor_covers` needs none); under the kernel
invariants the thread sits on one core and at most one flag is raised.  The
queue membership and the current slot are read from `st` because a key writer
moves neither (the placements that do mark the core themselves).  A write that
left no TCB under `tid` counts as a moved key. -/
def markKeyChangeFor (st : SystemState) (tid : SeLe4n.ThreadId)
    (preKey : SeLe4n.Priority × SeLe4n.Deadline) : SystemState :=
  let postKey? := (st.getTcb? tid).map (resolveEffectivePrioDeadline st)
  let moved : Bool := match postKey? with
    | some k => !(preKey.1 == k.1 && preKey.2.val == k.2.val)
    | none => true
  let weakened : Bool := match postKey? with
    | some k => k.1.val < preKey.1.val || preKey.2.val < k.2.val
    | none => false
  let staled : CoreId → Bool := fun c =>
    (moved && (st.scheduler.runQueueOnCore c).contains tid) ||
      (weakened && st.scheduler.currentOnCore c == some tid)
  markReschedulePendingWhere st staled allCores

/-- Any projection that the flag write leaves alone, the hook leaves alone:
the hook is a sequence of `markReschedulePendingOnCore`s. -/
theorem markKeyChangeFor_extract_frame {F : Type} (extract : SystemState → F)
    (st : SystemState) (tid : SeLe4n.ThreadId) (k : SeLe4n.Priority × SeLe4n.Deadline)
    (h : ∀ (s : SystemState) c, extract (s.markReschedulePendingOnCore c) = extract s) :
    extract (markKeyChangeFor st tid k) = extract st := by
  unfold markKeyChangeFor
  exact markReschedulePendingWhere_extract_frame extract h st _ allCores

/-- The key hook for a writer that hands in its **pre-state** rather than a key
it already read: `tid`'s key is read on `pre`, the flags are raised on `post`.
A thread with no TCB in `pre` had no key, so every core still holding it in a
queue or the current slot is flagged.  The binding writers (donation, its
return, the donation cancels) end in this, once per thread whose binding they
moved. -/
def markKeyChangeFrom (pre post : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match pre.getTcb? tid with
  | some tcb => markKeyChangeFor post tid (resolveEffectivePrioDeadline pre tcb)
  | none => markReschedulePendingWhere post
      (fun c => (post.scheduler.runQueueOnCore c).contains tid ||
        post.scheduler.currentOnCore c == some tid) allCores

theorem markKeyChangeFrom_extract_frame {F : Type} (extract : SystemState → F)
    (pre post : SystemState) (tid : SeLe4n.ThreadId)
    (h : ∀ (s : SystemState) c, extract (s.markReschedulePendingOnCore c) = extract s) :
    extract (markKeyChangeFrom pre post tid) = extract post := by
  unfold markKeyChangeFrom
  split
  · exact markKeyChangeFor_extract_frame extract post tid _ h
  · exact markReschedulePendingWhere_extract_frame extract h post _ allCores

/-- The `.reschedule` SGIs a step owes, from the flag vector captured before
dispatch and the committed state's: one per core other than the executing core
whose flag went `false → true`.  A core already pending at the step's start is
not re-poked (its SGI is outstanding), which is the "modulo cores already
pending" clause of the row's set-equality target. -/
def rescheduleSgisFromFlags (pre post : Vector Bool numCores) (e : CoreId) :
    List (CoreId × SgiKind) :=
  (allCores.filter fun c => c != e && !pre.get c && post.get c).map
    fun c => (c, SgiKind.reschedule)

/-- Membership in the flag-derived list, spelled out. -/
theorem mem_rescheduleSgisFromFlags_iff (pre post : Vector Bool numCores) (e c : CoreId)
    (k : SgiKind) :
    (c, k) ∈ rescheduleSgisFromFlags pre post e ↔
      k = SgiKind.reschedule ∧ c ≠ e ∧ pre.get c = false ∧ post.get c = true := by
  unfold rescheduleSgisFromFlags
  simp only [List.mem_map, List.mem_filter, Concurrency.mem_allCores, true_and, Prod.mk.injEq]
  constructor
  · intro h
    obtain ⟨c', hc', hEq⟩ := h
    obtain ⟨rfl, rfl⟩ := hEq
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hc'
    exact ⟨rfl, hc'.1.1, hc'.1.2, hc'.2⟩
  · rintro ⟨rfl, hne, hpre, hpost⟩
    exact ⟨c, by simp [hne, hpre, hpost], rfl, rfl⟩

/-- Every flag-derived SGI is a `.reschedule` (the counterpart of
`computeCrossCoreSgis_all_reschedule`). -/
theorem rescheduleSgisFromFlags_all_reschedule (pre post : Vector Bool numCores) (e : CoreId)
    (p : CoreId × SgiKind) (h : p ∈ rescheduleSgisFromFlags pre post e) :
    p.2 = SgiKind.reschedule := by
  obtain ⟨c, k⟩ := p
  exact ((mem_rescheduleSgisFromFlags_iff pre post e c k).mp h).1

/-- The executing core never pokes itself (the counterpart of
`currentSlotChangeSgis_not_execCore`). -/
theorem rescheduleSgisFromFlags_not_execCore (pre post : Vector Bool numCores) (e c : CoreId)
    (k : SgiKind) (h : (c, k) ∈ rescheduleSgisFromFlags pre post e) : c ≠ e :=
  ((mem_rescheduleSgisFromFlags_iff pre post e c k).mp h).2.1

/-- A flag that was already set surfaces nothing — the list names only the
cores this step raised. -/
theorem rescheduleSgisFromFlags_nil_of_eq (v : Vector Bool numCores) (e : CoreId) :
    rescheduleSgisFromFlags v v e = [] := by
  unfold rescheduleSgisFromFlags
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro c _
  cases v.get c <;> simp

/-! ### Frames: the key hook writes one flag and nothing else -/

@[simp] theorem markKeyChangeFor_objects (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).objects = st.objects :=
  markKeyChangeFor_extract_frame (fun s => s.objects) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_objectIndex (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).objectIndex = st.objectIndex :=
  markKeyChangeFor_extract_frame (fun s => s.objectIndex) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_machine (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).machine = st.machine :=
  markKeyChangeFor_extract_frame (fun s => s.machine) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_cdt (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).cdt = st.cdt :=
  markKeyChangeFor_extract_frame (fun s => s.cdt) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_cdtNodeSlot (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).cdtNodeSlot = st.cdtNodeSlot :=
  markKeyChangeFor_extract_frame (fun s => s.cdtNodeSlot) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_scThreadIndex (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).scThreadIndex = st.scThreadIndex :=
  markKeyChangeFor_extract_frame (fun s => s.scThreadIndex) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_irqHandlers (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).irqHandlers = st.irqHandlers :=
  markKeyChangeFor_extract_frame (fun s => s.irqHandlers) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_tlbShootdown (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).tlbShootdown = st.tlbShootdown :=
  markKeyChangeFor_extract_frame (fun s => s.tlbShootdown) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_perCoreTlb (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).perCoreTlb = st.perCoreTlb :=
  markKeyChangeFor_extract_frame (fun s => s.perCoreTlb) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_perCoreICache (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).perCoreICache = st.perCoreICache :=
  markKeyChangeFor_extract_frame (fun s => s.perCoreICache) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_pendingIcacheMaintenance (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).pendingIcacheMaintenance = st.pendingIcacheMaintenance :=
  markKeyChangeFor_extract_frame (fun s => s.pendingIcacheMaintenance) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_pendingPhysicalWrites (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).pendingPhysicalWrites = st.pendingPhysicalWrites :=
  markKeyChangeFor_extract_frame (fun s => s.pendingPhysicalWrites) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_serviceRegistry (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).serviceRegistry = st.serviceRegistry :=
  markKeyChangeFor_extract_frame (fun s => s.serviceRegistry) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_objectIndexSet (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).objectIndexSet = st.objectIndexSet :=
  markKeyChangeFor_extract_frame (fun s => s.objectIndexSet) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_services (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).services = st.services :=
  markKeyChangeFor_extract_frame (fun s => s.services) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_lifecycle (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).lifecycle = st.lifecycle :=
  markKeyChangeFor_extract_frame (fun s => s.lifecycle) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_asidTable (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).asidTable = st.asidTable :=
  markKeyChangeFor_extract_frame (fun s => s.asidTable) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_interfaceRegistry (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).interfaceRegistry = st.interfaceRegistry :=
  markKeyChangeFor_extract_frame (fun s => s.interfaceRegistry) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_cdtSlotNode (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).cdtSlotNode = st.cdtSlotNode :=
  markKeyChangeFor_extract_frame (fun s => s.cdtSlotNode) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_cdtNextNode (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).cdtNextNode = st.cdtNextNode :=
  markKeyChangeFor_extract_frame (fun s => s.cdtNextNode) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_tlb (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).tlb = st.tlb :=
  markKeyChangeFor_extract_frame (fun s => s.tlb) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_objStoreLock (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).objStoreLock = st.objStoreLock :=
  markKeyChangeFor_extract_frame (fun s => s.objStoreLock) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_schedulerLocks (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).schedulerLocks = st.schedulerLocks :=
  markKeyChangeFor_extract_frame (fun s => s.schedulerLocks) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_declassificationAuditLog (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).declassificationAuditLog = st.declassificationAuditLog :=
  markKeyChangeFor_extract_frame (fun s => s.declassificationAuditLog) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_declassificationAuditEpoch (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).declassificationAuditEpoch = st.declassificationAuditEpoch :=
  markKeyChangeFor_extract_frame (fun s => s.declassificationAuditEpoch) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_declassificationRefusals (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).declassificationRefusals = st.declassificationRefusals :=
  markKeyChangeFor_extract_frame (fun s => s.declassificationRefusals) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_declassificationTaint (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).declassificationTaint = st.declassificationTaint :=
  markKeyChangeFor_extract_frame (fun s => s.declassificationTaint) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_getTcb? (st : SystemState) (tid tid' : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).getTcb? tid' = st.getTcb? tid' := by
  unfold SystemState.getTcb?; rw [markKeyChangeFor_objects]

@[simp] theorem markKeyChangeFor_getSchedContext? (st : SystemState) (tid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).getSchedContext? scId = st.getSchedContext? scId := by
  unfold SystemState.getSchedContext?; rw [markKeyChangeFor_objects]

@[simp] theorem markKeyChangeFor_runQueueOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) (c : CoreId) :
    (markKeyChangeFor st tid k).scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.runQueueOnCore c) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_currentOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) (c : CoreId) :
    (markKeyChangeFor st tid k).scheduler.currentOnCore c = st.scheduler.currentOnCore c :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.currentOnCore c) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_replenishQueueOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) (c : CoreId) :
    (markKeyChangeFor st tid k).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.replenishQueueOnCore c) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_activeDomainOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) (c : CoreId) :
    (markKeyChangeFor st tid k).scheduler.activeDomainOnCore c
      = st.scheduler.activeDomainOnCore c :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.activeDomainOnCore c) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_domainTimeRemainingOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) (c : CoreId) :
    (markKeyChangeFor st tid k).scheduler.domainTimeRemainingOnCore c
      = st.scheduler.domainTimeRemainingOnCore c :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.domainTimeRemainingOnCore c) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_domainScheduleIndexOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) (c : CoreId) :
    (markKeyChangeFor st tid k).scheduler.domainScheduleIndexOnCore c
      = st.scheduler.domainScheduleIndexOnCore c :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.domainScheduleIndexOnCore c) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_lastTimeoutErrorsOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) (c : CoreId) :
    (markKeyChangeFor st tid k).scheduler.lastTimeoutErrorsOnCore c
      = st.scheduler.lastTimeoutErrorsOnCore c :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.lastTimeoutErrorsOnCore c) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_domainSchedule (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).scheduler.domainSchedule = st.scheduler.domainSchedule :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.domainSchedule) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_configDefaultTimeSlice (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline) :
    (markKeyChangeFor st tid k).scheduler.configDefaultTimeSlice = st.scheduler.configDefaultTimeSlice :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.configDefaultTimeSlice) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

/-- Queue membership on some core reads the run queues alone, which the hook
never writes. -/
@[simp] theorem markKeyChangeFor_runnableOnSomeCore (st : SystemState)
    (tid tid' : SeLe4n.ThreadId) (k : SeLe4n.Priority × SeLe4n.Deadline) :
    runnableOnSomeCore (markKeyChangeFor st tid k) tid' = runnableOnSomeCore st tid' := by
  unfold runnableOnSomeCore
  simp only [markKeyChangeFor_runQueueOnCore]

/-- The placement resolver reads the run queues and current slots alone, which
the hook never writes. -/
@[simp] theorem markKeyChangeFor_placedCoreOf? (st : SystemState)
    (tid tid' : SeLe4n.ThreadId) (k : SeLe4n.Priority × SeLe4n.Deadline) :
    placedCoreOf? (markKeyChangeFor st tid k) tid' = placedCoreOf? st tid' := by
  unfold placedCoreOf?
  simp only [markKeyChangeFor_runQueueOnCore, markKeyChangeFor_currentOnCore]

/-- Marking one core never lowers another's flag (nor its own). -/
theorem _root_.SeLe4n.Model.SchedulerState.markReschedulePendingOnCore_reschedulePendingOnCore_of
    (s : SchedulerState) (c c' : CoreId) (h : s.reschedulePendingOnCore c = true) :
    (s.markReschedulePendingOnCore c').reschedulePendingOnCore c = true := by
  by_cases hc : c' = c
  · subst hc; simp
  · simp [hc, h]

/-- The hook never lowers a flag: a core pending before it is pending after. -/
theorem markKeyChangeFor_reschedulePendingOnCore_mono (st : SystemState)
    (tid : SeLe4n.ThreadId) (k : SeLe4n.Priority × SeLe4n.Deadline) (c : CoreId)
    (h : st.scheduler.reschedulePendingOnCore c = true) :
    (markKeyChangeFor st tid k).scheduler.reschedulePendingOnCore c = true := by
  simp only [markKeyChangeFor, markReschedulePendingWhere_reschedulePendingOnCore,
    h, Bool.true_or]

/-! ### Frames: the pre-state form of the hook writes flags and nothing else -/

@[simp] theorem markKeyChangeFrom_objects (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).objects = st.objects :=
  markKeyChangeFrom_extract_frame (fun s => s.objects) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_objectIndex (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).objectIndex = st.objectIndex :=
  markKeyChangeFrom_extract_frame (fun s => s.objectIndex) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_machine (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).machine = st.machine :=
  markKeyChangeFrom_extract_frame (fun s => s.machine) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_cdt (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).cdt = st.cdt :=
  markKeyChangeFrom_extract_frame (fun s => s.cdt) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_cdtNodeSlot (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).cdtNodeSlot = st.cdtNodeSlot :=
  markKeyChangeFrom_extract_frame (fun s => s.cdtNodeSlot) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_scThreadIndex (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).scThreadIndex = st.scThreadIndex :=
  markKeyChangeFrom_extract_frame (fun s => s.scThreadIndex) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_irqHandlers (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).irqHandlers = st.irqHandlers :=
  markKeyChangeFrom_extract_frame (fun s => s.irqHandlers) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_tlbShootdown (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).tlbShootdown = st.tlbShootdown :=
  markKeyChangeFrom_extract_frame (fun s => s.tlbShootdown) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_perCoreTlb (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).perCoreTlb = st.perCoreTlb :=
  markKeyChangeFrom_extract_frame (fun s => s.perCoreTlb) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_perCoreICache (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).perCoreICache = st.perCoreICache :=
  markKeyChangeFrom_extract_frame (fun s => s.perCoreICache) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_pendingIcacheMaintenance (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).pendingIcacheMaintenance = st.pendingIcacheMaintenance :=
  markKeyChangeFrom_extract_frame (fun s => s.pendingIcacheMaintenance) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_pendingPhysicalWrites (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).pendingPhysicalWrites = st.pendingPhysicalWrites :=
  markKeyChangeFrom_extract_frame (fun s => s.pendingPhysicalWrites) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_serviceRegistry (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).serviceRegistry = st.serviceRegistry :=
  markKeyChangeFrom_extract_frame (fun s => s.serviceRegistry) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_objectIndexSet (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).objectIndexSet = st.objectIndexSet :=
  markKeyChangeFrom_extract_frame (fun s => s.objectIndexSet) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_services (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).services = st.services :=
  markKeyChangeFrom_extract_frame (fun s => s.services) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_lifecycle (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).lifecycle = st.lifecycle :=
  markKeyChangeFrom_extract_frame (fun s => s.lifecycle) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_asidTable (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).asidTable = st.asidTable :=
  markKeyChangeFrom_extract_frame (fun s => s.asidTable) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_interfaceRegistry (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).interfaceRegistry = st.interfaceRegistry :=
  markKeyChangeFrom_extract_frame (fun s => s.interfaceRegistry) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_cdtSlotNode (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).cdtSlotNode = st.cdtSlotNode :=
  markKeyChangeFrom_extract_frame (fun s => s.cdtSlotNode) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_cdtNextNode (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).cdtNextNode = st.cdtNextNode :=
  markKeyChangeFrom_extract_frame (fun s => s.cdtNextNode) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_tlb (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).tlb = st.tlb :=
  markKeyChangeFrom_extract_frame (fun s => s.tlb) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_objStoreLock (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).objStoreLock = st.objStoreLock :=
  markKeyChangeFrom_extract_frame (fun s => s.objStoreLock) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_schedulerLocks (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).schedulerLocks = st.schedulerLocks :=
  markKeyChangeFrom_extract_frame (fun s => s.schedulerLocks) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_declassificationAuditLog (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).declassificationAuditLog = st.declassificationAuditLog :=
  markKeyChangeFrom_extract_frame (fun s => s.declassificationAuditLog) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_declassificationAuditEpoch (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).declassificationAuditEpoch = st.declassificationAuditEpoch :=
  markKeyChangeFrom_extract_frame (fun s => s.declassificationAuditEpoch) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_declassificationRefusals (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).declassificationRefusals = st.declassificationRefusals :=
  markKeyChangeFrom_extract_frame (fun s => s.declassificationRefusals) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_declassificationTaint (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).declassificationTaint = st.declassificationTaint :=
  markKeyChangeFrom_extract_frame (fun s => s.declassificationTaint) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_getTcb? (pre st : SystemState) (tid tid' : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).getTcb? tid' = st.getTcb? tid' := by
  unfold SystemState.getTcb?; rw [markKeyChangeFrom_objects]

@[simp] theorem markKeyChangeFrom_getSchedContext? (pre st : SystemState) (tid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) :
    (markKeyChangeFrom pre st tid).getSchedContext? scId = st.getSchedContext? scId := by
  unfold SystemState.getSchedContext?; rw [markKeyChangeFrom_objects]

@[simp] theorem markKeyChangeFrom_runQueueOnCore (pre st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    (markKeyChangeFrom pre st tid).scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.runQueueOnCore c) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_currentOnCore (pre st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    (markKeyChangeFrom pre st tid).scheduler.currentOnCore c = st.scheduler.currentOnCore c :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.currentOnCore c) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_replenishQueueOnCore (pre st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    (markKeyChangeFrom pre st tid).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.replenishQueueOnCore c) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_activeDomainOnCore (pre st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    (markKeyChangeFrom pre st tid).scheduler.activeDomainOnCore c
      = st.scheduler.activeDomainOnCore c :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.activeDomainOnCore c) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_domainTimeRemainingOnCore (pre st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    (markKeyChangeFrom pre st tid).scheduler.domainTimeRemainingOnCore c
      = st.scheduler.domainTimeRemainingOnCore c :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.domainTimeRemainingOnCore c) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_domainScheduleIndexOnCore (pre st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    (markKeyChangeFrom pre st tid).scheduler.domainScheduleIndexOnCore c
      = st.scheduler.domainScheduleIndexOnCore c :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.domainScheduleIndexOnCore c) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_lastTimeoutErrorsOnCore (pre st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    (markKeyChangeFrom pre st tid).scheduler.lastTimeoutErrorsOnCore c
      = st.scheduler.lastTimeoutErrorsOnCore c :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.lastTimeoutErrorsOnCore c) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_domainSchedule (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).scheduler.domainSchedule = st.scheduler.domainSchedule :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.domainSchedule) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_configDefaultTimeSlice (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).scheduler.configDefaultTimeSlice = st.scheduler.configDefaultTimeSlice :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.configDefaultTimeSlice) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_runnableOnSomeCore (pre st : SystemState)
    (tid tid' : SeLe4n.ThreadId) :
    runnableOnSomeCore (markKeyChangeFrom pre st tid) tid' = runnableOnSomeCore st tid' := by
  unfold runnableOnSomeCore
  simp only [markKeyChangeFrom_runQueueOnCore]

@[simp] theorem markKeyChangeFrom_placedCoreOf? (pre st : SystemState)
    (tid tid' : SeLe4n.ThreadId) :
    placedCoreOf? (markKeyChangeFrom pre st tid) tid' = placedCoreOf? st tid' := by
  unfold placedCoreOf?
  simp only [markKeyChangeFrom_runQueueOnCore, markKeyChangeFrom_currentOnCore]

@[simp] theorem markKeyChangeFrom_getObject? (pre st : SystemState) (tid : SeLe4n.ThreadId)
    (oid : SeLe4n.ObjId) :
    (markKeyChangeFrom pre st tid).getObject? oid = st.getObject? oid := by
  unfold SystemState.getObject?; rw [markKeyChangeFrom_objects]

@[simp] theorem markKeyChangeFrom_getReply? (pre st : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) :
    (markKeyChangeFrom pre st tid).getReply? rid = st.getReply? rid := by
  unfold SystemState.getReply?; rw [markKeyChangeFrom_objects]

/-- The hook writes the scheduler record only: the state after it is the state
before it with the hook's scheduler.  The form a store-chain decomposition
states its final step in, so every non-scheduler reading of the step is
definitional. -/
theorem markKeyChangeFrom_eq_with_scheduler (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    markKeyChangeFrom pre st tid =
      { st with scheduler := (markKeyChangeFrom pre st tid).scheduler } :=
  markKeyChangeFrom_extract_frame
    (fun s => ({ s with scheduler := (markKeyChangeFrom pre st tid).scheduler } : SystemState))
    pre st tid (fun _ _ => rfl)

/-- Two hooks in a row (a binding writer's pair) write the reschedule flags
only: the result is its input with the result's flag vector and its own
`scThreadIndex` — the form the donation and return store chains state their
last step in, so every other reading of the step is definitional. -/
theorem markKeyChangeFrom_twice_eq_with (pre X : SystemState) (a b : SeLe4n.ThreadId) :
    markKeyChangeFrom pre (markKeyChangeFrom pre X a) b =
      { X with
          scheduler := { X.scheduler with reschedulePending :=
            (markKeyChangeFrom pre (markKeyChangeFrom pre X a) b).scheduler.reschedulePending },
          scThreadIndex := (markKeyChangeFrom pre (markKeyChangeFrom pre X a) b).scThreadIndex } :=
  let Y := markKeyChangeFrom pre (markKeyChangeFrom pre X a) b
  let f := fun s : SystemState =>
    ({ s with scheduler := { s.scheduler with reschedulePending := Y.scheduler.reschedulePending },
              scThreadIndex := Y.scThreadIndex } : SystemState)
  (markKeyChangeFrom_extract_frame f pre _ b (fun _ _ => rfl)).trans
    (markKeyChangeFrom_extract_frame f pre X a (fun _ _ => rfl))

/-- An unchanged scheduler is in particular unchanged except for its flags —
the bridge from a whole-scheduler frame to the binding writers' form. -/
theorem schedulerEqExceptReschedule_of_eq {a b : SystemState}
    (h : a.scheduler = b.scheduler) :
    a.scheduler = { b.scheduler with reschedulePending := a.scheduler.reschedulePending } := by
  rw [h]

end SeLe4n.Kernel
