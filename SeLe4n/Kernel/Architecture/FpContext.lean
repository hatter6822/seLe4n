-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.TrapFrameSave
import SeLe4n.Kernel.Scheduler.IdleThread

/-!
# WS-BP BP7.9 — per-thread FP/SIMD state, switched lazily

`boot.S` traps FP/SIMD at EL0 and EL1 (`CPACR_EL1 := 0`), so until this cut a
user FP instruction raised EC `0x07` and was delivered as a `userException`
fault: fail-closed, and no thread could use floating point.  Each thread now has
an FP context (`TCB.fpContext`: `v0`–`v31`, `FPCR`, `FPSR`) and each core an
**owner** (`MachineState.fpOwner`): the thread whose values its registers hold.

## The two transitions

* **`fpAccessOnCore`** — EC `0x07` from EL0.  The core's current thread asked
  for FP/SIMD; if the core's registers hold another thread's live values they
  are saved into that thread's TCB first (the entry captured them), then the
  current thread becomes the owner and its own saved context is what the HAL
  loads, after which the trap is lifted and the instruction restarts.
* **`fpReleaseOnCore`** — the first entry whose committed state no longer runs a
  core's owner there saves the owner's live values into its TCB and clears the
  ownership, so the trap is armed again for whatever the core resumes.

## Where this departs from seL4, and why

seL4's `CONFIG_HAVE_FPU` switch saves the previous owner only when a *new* thread
traps on the same core, and moves a thread's live state between cores with an IPI
when its affinity changes.  This kernel's placement is not fixed by affinity — an
unpinned thread is woken onto the boot core wherever it last ran — so pure
per-core laziness would need that cross-core release on every such move.  The
release therefore happens at the entry that switches the owner out, which keeps
a thread's context in its TCB whenever it is not running, so a trap on **any**
core can load it.  The load stays lazy: a thread that never touches FP/SIMD
costs nothing, and one that does pays one trap per dispatch.

One race survives the release: a thread taken off a remote core's `current` slot
(a suspend, say) and dispatched elsewhere before that core has taken the SGI the
change sent it.  Its live values are still in the first core's registers, so
`fpAccessOnCore` answers **retry** — the trap stays armed, the thread
re-executes the instruction, and it traps again until the first core's
reschedule entry has released it (`fpOwnedElsewhere`).  Loading the stale TCB
copy instead would silently lose the thread's work.

## Information flow

The FP context is the thread's own register state: `projectKernelObject` erases
it, and no transition here lets a thread read another's.  The load is the
current thread's own saved context (`fpAccessOnCore_load_eq_own_context`), and
the only TCB the captured live values are written into is the core's recorded
owner, whose values those registers hold.  What a core's registers hold after a
destroyed owner — the destroy path refuses a thread that owns a core's registers
(`MachineState.fpOwnedOnSomeCore`), so an owner is never replaced under its id — is
overwritten whole by the next load.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

/-- **WS-BP BP7.9**: the owner of core `c`'s FP/SIMD registers. -/
@[inline] def fpOwnerOf (st : SystemState) (c : CoreId) : Option SeLe4n.ThreadId :=
  st.machine.fpOwnerOnCore c

/-- **WS-BP BP7.9**: write a thread's saved FP/SIMD context — the typed
read-modify-write, so an absent thread is left absent. -/
def writeFpContextToTcb (st : SystemState) (tid : SeLe4n.ThreadId) (ctx : FpContext) :
    SystemState :=
  st.updateTcb tid fun tcb => { tcb with fpContext := ctx }

/-- **WS-BP BP7.9**: record `t?` as the owner of core `c`'s FP/SIMD registers. -/
def setFpOwner (st : SystemState) (c : CoreId) (t? : Option SeLe4n.ThreadId) : SystemState :=
  { st with machine := st.machine.setFpOwnerOnCore c t? }

/-- **WS-BP BP7.9**: some core other than `c` holds `tid`'s live FP/SIMD values. -/
def fpOwnedElsewhere (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) : Bool :=
  allCores.any fun d => decide (d ≠ c) && fpOwnerOf st d == some tid

/-- **WS-BP BP7.9**: the core resumes its FP owner, so the trap is lifted. -/
def fpLiveFor (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) : Bool :=
  fpOwnerOf st c == some tid

/-- WS-ZA ZA2.2: `fpLiveFor` as compiled — compared with `Option.isEqSome`, so
no `some tid` is built for the comparison. -/
def fpLiveForImpl (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) : Bool :=
  (fpOwnerOf st c).isEqSome tid

@[csimp] theorem fpLiveFor_eq_impl : @fpLiveFor = @fpLiveForImpl := by
  funext st c tid
  unfold fpLiveFor fpLiveForImpl
  cases fpOwnerOf st c <;> rfl

/-- **WS-BP BP7.9**: what an FP/SIMD access trap does. -/
inductive FpAccessOutcome where
  /-- Load this context into the registers and lift the trap. -/
  | load (ctx : FpContext)
  /-- The thread's live values are on another core: leave the trap armed and
  let the thread re-execute the instruction. -/
  | retry
  /-- No user thread runs here: nothing to do. -/
  | inert
  deriving Inhabited, DecidableEq

/-- **WS-BP BP7.9: EC `0x07` from EL0 on core `c`.**

`live` is what the entry captured from the core's registers — `some` exactly
when the core has an owner, since only then do the registers hold anything the
model tracks.  An owner without a capture answers `.retry` rather than dropping
the owner's live values. -/
def fpAccessOnCore (st : SystemState) (c : CoreId) (live : Option FpContext) :
    FpAccessOutcome × SystemState :=
  match st.scheduler.currentOnCore c with
  | none => (.inert, st)
  | some tid =>
    if SeLe4n.Kernel.isIdleThreadId tid then (.inert, st)
    else if fpOwnedElsewhere st c tid then (.retry, st)
    else
      match fpOwnerOf st c, live with
      | some _, none => (.retry, st)
      | owner?, _ =>
        let st1 := match owner?, live with
          | some o, some ctx => writeFpContextToTcb st o ctx
          | _, _ => st
        let st2 := setFpOwner st1 c (some tid)
        (.load (((st2.getTcb? tid).map (·.fpContext)).getD default), st2)

/-- **WS-BP BP7.9**: the owner a core must release — its recorded owner, when
the core's committed state no longer runs it. -/
def fpReleaseNeeded (st : SystemState) (c : CoreId) : Option SeLe4n.ThreadId :=
  match fpOwnerOf st c with
  | some o => if st.scheduler.currentOnCore c = some o then none else some o
  | none => none

/-- **WS-BP BP7.9: release a core's switched-out FP owner**: its live values,
captured from the registers, become its saved context, and the core owns
nobody's. -/
def fpReleaseOnCore (st : SystemState) (c : CoreId) (live : FpContext) : SystemState :=
  match fpReleaseNeeded st c with
  | some o => setFpOwner (writeFpContextToTcb st o live) c none
  | none => st

-- ============================================================================
-- Frames
-- ============================================================================

theorem writeFpContextToTcb_scheduler (st : SystemState) (tid : SeLe4n.ThreadId)
    (ctx : FpContext) : (writeFpContextToTcb st tid ctx).scheduler = st.scheduler :=
  SystemState.updateTcb_scheduler st tid _

theorem writeFpContextToTcb_machine (st : SystemState) (tid : SeLe4n.ThreadId)
    (ctx : FpContext) : (writeFpContextToTcb st tid ctx).machine = st.machine :=
  SystemState.updateTcb_machine st tid _

@[simp] theorem setFpOwner_scheduler (st : SystemState) (c : CoreId)
    (t? : Option SeLe4n.ThreadId) : (setFpOwner st c t?).scheduler = st.scheduler := rfl

@[simp] theorem setFpOwner_objects (st : SystemState) (c : CoreId)
    (t? : Option SeLe4n.ThreadId) : (setFpOwner st c t?).objects = st.objects := rfl

@[simp] theorem setFpOwner_getTcb? (st : SystemState) (c : CoreId)
    (t? : Option SeLe4n.ThreadId) (tid : SeLe4n.ThreadId) :
    (setFpOwner st c t?).getTcb? tid = st.getTcb? tid := rfl

/-- **WS-BP BP7.9**: an FP access schedules nothing. -/
theorem fpAccessOnCore_scheduler (st : SystemState) (c : CoreId) (live : Option FpContext) :
    (fpAccessOnCore st c live).2.scheduler = st.scheduler := by
  unfold fpAccessOnCore
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split <;> simp [writeFpContextToTcb_scheduler]

/-- **WS-BP BP7.9**: and neither does a release. -/
theorem fpReleaseOnCore_scheduler (st : SystemState) (c : CoreId) (live : FpContext) :
    (fpReleaseOnCore st c live).scheduler = st.scheduler := by
  unfold fpReleaseOnCore
  split
  · simp [writeFpContextToTcb_scheduler]
  · rfl

-- ============================================================================
-- What the transitions guarantee
-- ============================================================================

/-- **WS-BP BP7.9: the context loaded is the faulting thread's own.**  Whatever
the core's registers held before, the HAL is handed the saved context of the
thread the core runs — the property that keeps one thread's FP state out of
another's reach — and that thread is now the core's owner. -/
theorem fpAccessOnCore_load_eq_own_context (st : SystemState) (c : CoreId)
    (live : Option FpContext) (ctx : FpContext) (st' : SystemState)
    (h : fpAccessOnCore st c live = (.load ctx, st')) :
    ∃ tid, st.scheduler.currentOnCore c = some tid ∧
      SeLe4n.Kernel.isIdleThreadId tid = false ∧
      ctx = ((st'.getTcb? tid).map (·.fpContext)).getD default ∧
      fpOwnerOf st' c = some tid := by
  unfold fpAccessOnCore at h
  split at h
  · cases h
  · next tid hCur =>
    split at h
    · cases h
    · next hIdle =>
      split at h
      · cases h
      · split at h
        · cases h
        · simp only [Prod.mk.injEq, FpAccessOutcome.load.injEq] at h
          obtain ⟨hCtx, hSt⟩ := h
          subst hSt
          refine ⟨tid, hCur, by simpa using hIdle, hCtx.symm, ?_⟩
          simp [fpOwnerOf, setFpOwner]

/-- **WS-BP BP7.9: a thread whose live values are on another core is never
loaded from its stale saved copy** — the access retries until that core has
released it. -/
theorem fpAccessOnCore_retry_of_owned_elsewhere (st : SystemState) (c : CoreId)
    (live : Option FpContext) (tid : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hIdle : SeLe4n.Kernel.isIdleThreadId tid = false)
    (hElse : fpOwnedElsewhere st c tid = true) :
    fpAccessOnCore st c live = (.retry, st) := by
  simp [fpAccessOnCore, hCur, hIdle, hElse]

/-- **WS-BP BP7.9: the registers' live values are saved into their owner, and no
other thread.**  When the core's owner `o` is not the faulting thread, the
access writes the captured values into `o`'s context and leaves every other
thread's untouched. -/
theorem fpAccessOnCore_saves_owner (st : SystemState) (c : CoreId) (ctx : FpContext)
    (tid o : SeLe4n.ThreadId) (tcbO : TCB)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hIdle : SeLe4n.Kernel.isIdleThreadId tid = false)
    (hElse : fpOwnedElsewhere st c tid = false)
    (hOwner : fpOwnerOf st c = some o) (hO : st.getTcb? o = some tcbO)
    (hInv : st.objects.invExt) :
    (fpAccessOnCore st c (some ctx)).2.getTcb? o = some { tcbO with fpContext := ctx } ∧
    ∀ t, o.toObjId ≠ t.toObjId →
      (fpAccessOnCore st c (some ctx)).2.getTcb? t = st.getTcb? t := by
  simp only [fpAccessOnCore, hCur, hIdle, hElse, hOwner, Bool.false_eq_true, if_false,
    setFpOwner_getTcb?]
  refine ⟨?_, fun t hNe => ?_⟩
  · unfold writeFpContextToTcb
    rw [SystemState.updateTcb_getTcb?_self st o _ hInv, hO]; rfl
  · exact SystemState.updateTcb_getTcb?_ne st o _ hInv t hNe

/-- **WS-BP BP7.9: after a release the core owns nothing it does not run.** -/
theorem fpReleaseOnCore_owner (st : SystemState) (c : CoreId) (live : FpContext) :
    fpOwnerOf (fpReleaseOnCore st c live) c = none ∨
      (∃ o, fpOwnerOf (fpReleaseOnCore st c live) c = some o ∧
        st.scheduler.currentOnCore c = some o) := by
  unfold fpReleaseOnCore
  split
  · left
    simp [fpOwnerOf, setFpOwner, writeFpContextToTcb_machine]
  · next hNone =>
    unfold fpReleaseNeeded at hNone
    cases hO : fpOwnerOf st c with
    | none => left; rfl
    | some o =>
      rw [hO] at hNone
      simp only at hNone
      split at hNone
      · next hCur => right; exact ⟨o, rfl, hCur⟩
      · cases hNone

/-- **WS-BP BP7.9: a release saves the owner's live values into the owner.** -/
theorem fpReleaseOnCore_saves_owner (st : SystemState) (c : CoreId) (live : FpContext)
    (o : SeLe4n.ThreadId) (tcbO : TCB)
    (hNeed : fpReleaseNeeded st c = some o) (hO : st.getTcb? o = some tcbO)
    (hInv : st.objects.invExt) :
    (fpReleaseOnCore st c live).getTcb? o = some { tcbO with fpContext := live } ∧
    ∀ t, o.toObjId ≠ t.toObjId → (fpReleaseOnCore st c live).getTcb? t = st.getTcb? t := by
  simp only [fpReleaseOnCore, hNeed, setFpOwner_getTcb?]
  refine ⟨?_, fun t hNe => ?_⟩
  · unfold writeFpContextToTcb
    rw [SystemState.updateTcb_getTcb?_self st o _ hInv, hO]; rfl
  · exact SystemState.updateTcb_getTcb?_ne st o _ hInv t hNe

/-- **WS-BP BP7.9**: a core whose owner still runs there releases nothing. -/
theorem fpReleaseOnCore_of_running (st : SystemState) (c : CoreId) (live : FpContext)
    (o : SeLe4n.ThreadId) (hOwner : fpOwnerOf st c = some o)
    (hCur : st.scheduler.currentOnCore c = some o) :
    fpReleaseOnCore st c live = st := by
  simp [fpReleaseOnCore, fpReleaseNeeded, hOwner, hCur]

end SeLe4n.Kernel.Architecture
