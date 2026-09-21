-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Model.Object.Types

/-!
# Per-core idle-thread identities

The per-core idle-thread *identifiers* (`idleThreadIdBase`, `idleThreadId`, and
their injectivity witnesses).  These live in the scheduler layer (rather than in
`Platform.Boot` where the WS-SM SM4.G *bootstrap* installs them) because the
per-core scheduler dispatcher — `scheduleEffectiveOnCore`
(`Scheduler/Operations/Core.lean`) — must reference `idleThreadId` to run a
core's idle thread when nothing else is runnable, and the dispatcher is
*upstream* of `Platform.Boot` in the import graph.

The idle *TCB* lives here too since `v0.35.68` — `createIdleThread` (the
dispatched form) and `queuedIdleThread` (the enqueued form), with their field
lemmas — because the kernel model's idle enqueue (`enqueueIdleThreadOnCore`,
`Scheduler/Operations/IdleEnqueue.lean`) builds the TCB it stores, and that
operation is what the production boot now *runs*: `Platform.Boot.enqueueIdleThread`
is the kernel-model enqueue on the intermediate state's `state`, so the module
holding the TCB has to sit upstream of both.  Only the boot *installers*
(`installIdleThread`, `bootFromPlatformWithIdleThreads`, `enqueueIdleThread`)
remain in `Platform.Boot`, where the `IntermediateState` / `Builder` machinery
they carry witnesses through is; the SM5.E theorems
(`Scheduler/Operations/PerCoreIdle.lean`) consume all of it.

The capability predicate `capTargetsReservedIdleObject` (PR #889 review round
2) lives here too, because both consumers of the reservation — the syscall
resolution in `Kernel/API.lean` and the boot validation in `Platform.Boot` —
sit downstream of this module and must decide the same question.
-/

namespace SeLe4n.Kernel

open SeLe4n.Kernel.Concurrency (CoreId)

/-- **WS-SM SM4.G** (plan §3.7): reserved base ObjId for per-core idle
    threads.  The idle thread for core `c` lives at the `ObjId`
    `idleThreadIdBase + c.val`.  The value sits above the 16-bit ObjId space
    (`0x1_0000 = 65536`) that platform configs assign their objects from, so
    on the canonical platforms the per-core idle range
    `[idleThreadIdBase, idleThreadIdBase + numCores)` is disjoint from the
    config objects.

    The boot-install theorems (`bootFromPlatformWithIdleThreads_all_cores_have_idle`
    and the scheduler-bundle theorems) hold **unconditionally** — the idle TCB
    is installed regardless of the base config, because `createObject`'s insert
    is overwriting.  The disjointness is what guarantees the install does not
    *clobber* a config object: `idleSlotsFreshAt` is the freshness precondition,
    `bootFromPlatformWithIdleThreads_preserves_platform_objects` proves the
    install is purely additive under it, and
    `idleSlotsFreshAt_of_initialObjects_below_base` discharges freshness for any
    config whose objects live below `idleThreadIdBase` (the canonical case).
    The bound is **not** assumed for arbitrary configs. -/
def idleThreadIdBase : Nat := 0x1_0000

/-- **WS-SM SM4.G** (plan §3.7): the per-core idle thread's `ThreadId`.  Idle
    threads are injective in the core (`idleThreadId_injective`), so the
    per-core idle objects never alias one another. -/
def idleThreadId (c : CoreId) : SeLe4n.ThreadId :=
  SeLe4n.ThreadId.ofNat (idleThreadIdBase + c.val)

/-- **WS-SM SM4.G**: `idleThreadId` is injective in the core. -/
theorem idleThreadId_injective {c₁ c₂ : CoreId}
    (h : idleThreadId c₁ = idleThreadId c₂) : c₁ = c₂ := by
  unfold idleThreadId at h
  have hv : idleThreadIdBase + c₁.val = idleThreadIdBase + c₂.val :=
    SeLe4n.ThreadId.ofNat_injective h
  exact Fin.ext (Nat.add_left_cancel hv)

/-- **WS-SM SM4.G**: distinct cores get distinct idle-thread ids. -/
theorem idleThreadId_ne {c₁ c₂ : CoreId}
    (h : c₁ ≠ c₂) : idleThreadId c₁ ≠ idleThreadId c₂ :=
  fun hEq => h (idleThreadId_injective hEq)

/-- **WS-SM SM4.G**: distinct cores get distinct idle-thread `ObjId`s
    (the object-store key form of `idleThreadId_ne`). -/
theorem idleThreadId_toObjId_ne {c₁ c₂ : CoreId}
    (h : c₁ ≠ c₂) : (idleThreadId c₁).toObjId ≠ (idleThreadId c₂).toObjId := by
  intro hEq
  apply idleThreadId_ne h
  -- toObjId is `ObjId.ofNat ∘ toNat`; recover the ThreadId equality.
  have : (idleThreadId c₁).toNat = (idleThreadId c₂).toNat := by
    have h1 : (idleThreadId c₁).toObjId.val = (idleThreadId c₁).toNat := rfl
    have h2 : (idleThreadId c₂).toObjId.val = (idleThreadId c₂).toNat := rfl
    rw [← h1, ← h2, hEq]
  calc idleThreadId c₁ = SeLe4n.ThreadId.ofNat (idleThreadId c₁).toNat :=
          (SeLe4n.ThreadId.ofNat_toNat _).symm
    _ = SeLe4n.ThreadId.ofNat (idleThreadId c₂).toNat := by rw [this]
    _ = idleThreadId c₂ := SeLe4n.ThreadId.ofNat_toNat _

/-- **WS-RR RR5.4** (audit): is `tid` some core's idle thread?  Decides
    membership in the idle id range `[idleThreadIdBase, idleThreadIdBase + numCores)`,
    which `idleThreadId` enumerates exactly (`isIdleThreadId_iff`).

    The information-flow labeling guard excludes these ids from a deployment's
    declared separation witness (`separationWitnessAdmissible`,
    `InformationFlow/Policy.lean`): an idle thread is kernel-owned, issues no
    syscall and sends no message, so a labeling that differs only on idle threads
    separates nothing a flow decision can observe — the same reason the reserved
    sentinel is excluded. -/
def isIdleThreadId (tid : SeLe4n.ThreadId) : Bool :=
  idleThreadIdBase ≤ tid.toNat && tid.toNat < idleThreadIdBase + SeLe4n.Kernel.Concurrency.numCores

/-- **WS-RR RR5.4** (audit): every per-core idle id is recognised. -/
theorem isIdleThreadId_idleThreadId (c : CoreId) : isIdleThreadId (idleThreadId c) = true := by
  have hc := c.isLt
  simp only [isIdleThreadId, idleThreadId, SeLe4n.ThreadId.toNat, SeLe4n.ThreadId.ofNat,
    Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- **WS-RR RR5.4** (audit): the recogniser is exact — it accepts precisely the
    ids `idleThreadId` produces, so excluding what it accepts excludes the idle
    threads and nothing else. -/
theorem isIdleThreadId_iff (tid : SeLe4n.ThreadId) :
    isIdleThreadId tid = true ↔ ∃ c : CoreId, tid = idleThreadId c := by
  constructor
  · intro h
    simp only [isIdleThreadId, SeLe4n.ThreadId.toNat, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨⟨tid.val - idleThreadIdBase, by omega⟩, ?_⟩
    apply SeLe4n.ThreadId.ext
    show tid.val = idleThreadIdBase + (tid.val - idleThreadIdBase)
    omega
  · rintro ⟨c, rfl⟩
    exact isIdleThreadId_idleThreadId c

/-- **WS-RR RR5.13** (PR #889 review): is `oid` some core's idle **object** slot?
    The object-store key form of `isIdleThreadId`, for the boot validator: a
    platform config may not place an object at an idle slot, or the idle enqueue
    would overwrite it. -/
def isIdleObjId (oid : SeLe4n.ObjId) : Bool :=
  isIdleThreadId (SeLe4n.ThreadId.ofNat oid.toNat)

/-- **WS-RR RR5.13**: every idle thread's object slot is recognised. -/
theorem isIdleObjId_idleThreadId_toObjId (c : CoreId) :
    isIdleObjId (idleThreadId c).toObjId = true :=
  isIdleThreadId_idleThreadId c

/-- PR #889 review round 2: does `cap` name a **kernel-reserved idle object** —
    a per-core idle TCB, as the object itself or as a CNode to index into?
    seL4 has no capability to its idle thread at all; here the idle threads are
    ordinary objects in the store, so the reservation has to be decided
    wherever user authority names an object.  `syscallResolveCap` refuses such
    a capability (`syscallResolveCap_ok_not_reserved`), so no syscall can act on
    an idle TCB through a capability a boot CNode or a transfer happened to
    carry — a `.tcbSuspend` on one would remove the core's only guaranteed
    runnable thread — and `PlatformConfig.wellFormed` refuses a config that
    references one (`idleSlotsReserved`).  Total over `CapTarget`, so a new
    target kind must say where it stands. -/
def capTargetsReservedIdleObject (cap : SeLe4n.Model.Capability) : Bool :=
  match cap.target with
  | .object oid => isIdleObjId oid
  | .cnodeSlot cnode _ => isIdleObjId cnode
  | .replyCap _ => false
  | .auditTrail => false

/-- PR #889 review round 2: on an object capability the predicate is the idle
    test of its target. -/
theorem capTargetsReservedIdleObject_object (oid : SeLe4n.ObjId)
    (rights : SeLe4n.Model.AccessRightSet) (badge : Option SeLe4n.Badge) :
    capTargetsReservedIdleObject { target := .object oid, rights := rights, badge := badge } =
      isIdleObjId oid := rfl

/-- **WS-RR RR5.13**: a slot the recogniser rejects is no core's idle slot. -/
theorem idleThreadId_toObjId_ne_of_not_isIdleObjId (oid : SeLe4n.ObjId)
    (h : isIdleObjId oid = false) (c : CoreId) : (idleThreadId c).toObjId ≠ oid := by
  intro hEq
  rw [← hEq, isIdleObjId_idleThreadId_toObjId] at h
  exact Bool.noConfusion h

-- ============================================================================
-- The per-core idle TCB — its dispatched and its enqueued form (SM4.G / SM5.E.2;
-- moved here from `Platform.Boot` at v0.35.68, when the boot's idle install
-- became the kernel model's own enqueue)
-- ============================================================================

/-- **WS-SM SM4.G** (plan §3.7) / **WS-SM SM5.E.2** (plan §3.5): the per-core
    idle thread control block.

    Idle threads are the lowest-priority threads each core runs when nothing
    else is runnable.  Fields: `priority := ⟨0⟩` (lowest, so any runnable user
    thread always outranks idle — idle never starves a higher-priority thread),
    `domain := ⟨0⟩` (the boot active domain, so `currentThreadInActiveDomain`
    holds when the idle thread is current), `threadState := .Running` (it is the
    running thread when scheduled), `tid := idleThreadId c` (the per-core
    identity), and — **SM5.E.2** — `cpuAffinity := some c`: the idle thread is
    **pinned to its own core**.

    The affinity binding is the SM5.E.2 improvement.  `createIdleThread`
    predates `TCB.cpuAffinity` (which landed at SM5.B.4); now that the field
    exists, binding the idle thread to `some c` is what makes
    `idleThread_core_locality`
    (`Scheduler/Operations/PerCoreIdle.lean`) a *substantive* theorem rather
    than a frame fact: a thread bound to `some c` is not admitted onto any other
    core `c' ≠ c` (`affinityAdmitsCore`), so core `c`'s idle thread can never
    appear on core `c'`'s run queue.  `cspaceRoot` / `vspaceRoot` are
    `ObjId.sentinel`: an idle thread runs in kernel context and holds no
    capabilities, so it has no CSpace/VSpace root (this is semantically
    faithful, and the scheduler invariants never read these fields).  All other
    fields take their structure defaults.

    This is the *dispatched* form: SM4.G's `installIdleThread`
    (`Platform.Boot`) points a core's current slot at it.  The production boot
    stores the *enqueued* form, `queuedIdleThread`, below. -/
def createIdleThread (c : CoreId) : SeLe4n.Model.TCB :=
  { tid          := idleThreadId c
    priority     := ⟨0⟩
    domain       := ⟨0⟩
    cspaceRoot   := SeLe4n.ObjId.sentinel
    vspaceRoot   := SeLe4n.ObjId.sentinel
    ipcBuffer    := default
    threadState  := .Running
    cpuAffinity  := some c }

/-- **WS-RR RR5.11** (PR #889 review): the idle TCB as it is **enqueued** —
    `createIdleThread c` with `threadState := .Ready`.

    `createIdleThread` is the *dispatched* form: SM4.G's `installIdleThread`
    points a core's current slot at it, so `.Running` is the state the
    classification infers for it (`inferThreadState`: current on some core).  The
    kernel model's enqueue (`enqueueIdleThreadOnCore`) — and through it the
    production boot (`Platform.Boot.enqueueIdleThread`) — does the opposite: it
    puts idle on the core's run queue and leaves the current slot `none`, and the
    classification infers `.Ready` for a queued, non-current thread.  Storing the
    dispatched form on the enqueue path made every successful production boot
    violate `threadStateConsistent` on every core, which the harness never saw
    because `assertStateInvariantsFor` syncs the field before it checks it.  The
    stored field now says what the state says
    (`Platform.Boot.bootFromPlatformCheckedWithIdleThreads_idle_threadState`).

    Every other field is `createIdleThread`'s, so the enqueue-side theorems that
    read priority, domain, affinity or id go through by `rfl` exactly as before. -/
def queuedIdleThread (c : CoreId) : SeLe4n.Model.TCB :=
  { createIdleThread c with threadState := .Ready }

/-- WS-SM SM5.E.5 (plan §3.5, Theorem `idleThread_priority_zero`): the idle
    thread is priority `⟨0⟩` — the lowest schedulable priority.  Consequence: a
    runnable user thread (priority `> 0`, or even `0` with an earlier FIFO
    position) is never displaced by idle; idle is only selected when no
    higher-priority thread is eligible.  `rfl` from `createIdleThread`. -/
@[simp] theorem idleThread_priority_zero (c : CoreId) :
    (createIdleThread c).priority = ⟨0⟩ := rfl

/-- WS-SM SM5.E.5: the idle thread is in scheduling domain `⟨0⟩` (the boot
    active domain).  So when core `c`'s active domain is the boot domain (the RPi5
    v1.0.0 single-domain case, where `domainSchedule = []`), the idle thread is
    in-domain and hence an eligible selection candidate. -/
@[simp] theorem createIdleThread_domain_zero (c : CoreId) :
    (createIdleThread c).domain = ⟨0⟩ := rfl

/-- WS-SM SM5.E.2 (plan §3.5): the idle thread for core `c` is pinned to core
    `c` via `cpuAffinity = some c`.  This is the field that makes
    `idleThread_core_locality` substantive — `affinityAdmitsCore (createIdleThread
    c) c' = (c == c')`, so idle `c` is not admitted on any `c' ≠ c`. -/
@[simp] theorem createIdleThread_cpuAffinity (c : CoreId) :
    (createIdleThread c).cpuAffinity = some c := rfl

/-- WS-SM SM5.E.1: the idle thread's id is `idleThreadId c`. -/
@[simp] theorem createIdleThread_tid (c : CoreId) :
    (createIdleThread c).tid = idleThreadId c := rfl

/-- **WS-RR RR5.11** (PR #889 review): the **queued** idle TCB — what the enqueue
    surface stores — has `createIdleThread`'s priority, domain, affinity and id;
    only `threadState` differs (`.Ready`, `queuedIdleThread_threadState`), because
    a thread on a run queue and in no current slot is what `inferThreadState`
    classifies `.Ready`.  Each is `rfl`, so every enqueue-side theorem reads the
    field through these exactly as it read `createIdleThread`'s before. -/
@[simp] theorem queuedIdleThread_priority (c : CoreId) :
    (queuedIdleThread c).priority = ⟨0⟩ := rfl

@[simp] theorem queuedIdleThread_domain (c : CoreId) :
    (queuedIdleThread c).domain = ⟨0⟩ := rfl

@[simp] theorem queuedIdleThread_cpuAffinity (c : CoreId) :
    (queuedIdleThread c).cpuAffinity = some c := rfl

@[simp] theorem queuedIdleThread_tid (c : CoreId) :
    (queuedIdleThread c).tid = idleThreadId c := rfl

/-- **WS-RR RR5.11**: the queued idle TCB's state is `.Ready` — the fact the
    boot's consistency theorem rewrites with. -/
@[simp] theorem queuedIdleThread_threadState (c : CoreId) :
    (queuedIdleThread c).threadState = .Ready := rfl

/-- **WS-RR RR5.11**: the queued form differs from the dispatched form in the
    one field the state determines — the negative pin, so the two cannot silently
    collapse into one. -/
theorem queuedIdleThread_ne_createIdleThread (c : CoreId) :
    queuedIdleThread c ≠ createIdleThread c := by
  intro h
  have hState : SeLe4n.Model.ThreadState.Ready = SeLe4n.Model.ThreadState.Running :=
    congrArg SeLe4n.Model.TCB.threadState h
  cases hState

end SeLe4n.Kernel
