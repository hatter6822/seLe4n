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

end SeLe4n.Kernel
