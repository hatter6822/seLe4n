/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.CurrentNotResidentElsewhere

/-!
# No step writes the saved registers of a thread another core holds

WS-ZA ZA6.14.  Another core `d` holds a thread's registers in two ways: the
thread is `d`'s current thread (its frame is in flight on `d`), or it is `d`'s
resident thread (a remote deschedule left its live registers in `d`'s bank,
which `d`'s next entry saves into the thread, overwriting whatever the saved
context held).  A write to such a thread's saved registers would either be
lost at that save or disagree with the bank `d` resumes from.

`savedRegsKeptOffCore e pre post` says no step of core `e`'s entry does that:
every thread current or resident on a core other than `e` after the step has
the saved registers it had before.  It is stated on the post-state, so it
composes through the coverage relation's `currentKept` and `residentKept`
(`savedRegsKeptOffCore_trans`): a thread another core holds after two steps
was held there in between.

A step's census is read off what it writes (`savedRegsKeptOffCore_of_writes`):
it changes the saved registers only of threads that, at some earlier state
`base` of the same entry, no other core held (`offCoreFree`), and nothing
between `base` and the step's post-state made a thread current or resident on
another core.  The executing core's current thread is one
(`offCoreFree_of_current`, from `currentsUnique` and
`currentNotResidentElsewhere`), so the caller's own writes are censused here:
the register spill of the syscall's arguments (`writeFfiRegistersToTcb`), the
caller's return staging (`stageCallerReturnFor`) and the scheduling point's
save of the core's outgoing thread (`saveOutgoingContextOnCore`).

WS-ZA ZA6.15 adds the final delete's two kinds of write: the yield completion
(`completeYieldFrom`, whose yielder is linked, so no core holds it at an entry
boundary: `offCoreFree_of_yieldCode`) and the cancellation restore
(`restoreToReadyCancelled`, of a thread blocked in IPC).  The dispatch's arms
are ZA6.19 to ZA6.21, which consume these lemmas, with ZA6.16's invariant that
a thread blocked in IPC is resident on no core.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- A thread's saved register context, if it names a thread. -/
def _root_.SeLe4n.Model.SystemState.savedRegs (st : SystemState) (t : SeLe4n.ThreadId) :
    Option SeLe4n.RegisterFile :=
  (st.getTcb? t).map TCB.registerContext

/-- **No core other than `e` holds `t`**: `t` is neither current nor resident
on any other core. -/
def offCoreFree (e : CoreId) (st : SystemState) (t : SeLe4n.ThreadId) : Prop :=
  ∀ d, d ≠ e → st.scheduler.currentOnCore d ≠ some t ∧ st.machine.residentOnCore d ≠ some t

/-- WS-ZA ZA6.14: **the step writes the saved registers of no thread another core
holds**: every thread current or resident on a core other than the executing
core `e` after the step has the saved registers it had before. -/
def savedRegsKeptOffCore (e : CoreId) (pre post : SystemState) : Prop :=
  ∀ d, d ≠ e → ∀ t, (post.scheduler.currentOnCore d = some t ∨
      post.machine.residentOnCore d = some t) →
    post.savedRegs t = pre.savedRegs t

theorem savedRegsKeptOffCore_refl (e : CoreId) (st : SystemState) :
    savedRegsKeptOffCore e st st :=
  fun _ _ _ _ => rfl

/-- **The census composes**: a thread another core holds after the second step
was held there after the first (the second step's `currentKept` and
`residentKept`), so neither step wrote it. -/
theorem savedRegsKeptOffCore_trans {e : CoreId} {a b c : SystemState}
    (h₁ : savedRegsKeptOffCore e a b) (h₂ : savedRegsKeptOffCore e b c)
    (hK : currentKeptOffCore e b c) (hR : residentKeptOffCore e b c) :
    savedRegsKeptOffCore e a c := fun d hd t ht =>
  (h₂ d hd t ht).trans (h₁ d hd t (ht.imp (hK d hd t) (hR d hd t)))

/-- The census across a covered step (`stepCovers` carries both frames). -/
theorem savedRegsKeptOffCore_trans_stepCovers {e : CoreId} {a b c : SystemState}
    (h₁ : savedRegsKeptOffCore e a b) (h₂ : savedRegsKeptOffCore e b c)
    (hC : stepCovers e b c) : savedRegsKeptOffCore e a c :=
  savedRegsKeptOffCore_trans h₁ h₂ hC.currentKept hC.residentKept

/-- **A step's census, from what it writes**: it changes the saved registers
only of threads in `W`, each of which no other core held at an earlier state
`base`, and nothing from `base` to the step's post-state made a thread current
or resident on another core. -/
theorem savedRegsKeptOffCore_of_writes {e : CoreId} {base pre post : SystemState}
    (W : SeLe4n.ThreadId → Prop)
    (hOnly : ∀ t, ¬ W t → post.savedRegs t = pre.savedRegs t)
    (hFree : ∀ t, W t → offCoreFree e base t)
    (hK : currentKeptOffCore e base post) (hR : residentKeptOffCore e base post) :
    savedRegsKeptOffCore e pre post := fun d hd t ht => by
  refine hOnly t fun hW => ?_
  rcases ht with h | h
  · exact (hFree t hW d hd).1 (hK d hd t h)
  · exact (hFree t hW d hd).2 (hR d hd t h)

/-- A step that writes no thread's saved registers. -/
theorem savedRegsKeptOffCore_of_savedRegs_eq {e : CoreId} {pre post : SystemState}
    (h : ∀ t, post.savedRegs t = pre.savedRegs t) : savedRegsKeptOffCore e pre post :=
  fun _ _ t _ => h t

/-- **The executing core's current thread is held by no other core**: it is
current nowhere else (`currentsUnique`) and, idle or not, resident nowhere else
(`currentNotResidentElsewhere`: a non-idle current thread is resident on no
other core, and no core holds an idle thread's frame). -/
theorem offCoreFree_of_current {e : CoreId} {st : SystemState} {t : SeLe4n.ThreadId}
    (hCur : st.scheduler.currentOnCore e = some t) (hU : currentsUnique st)
    (hN : st.currentNotResidentElsewhere) : offCoreFree e st t := fun d hd => by
  refine ⟨fun h => hd (hU e d t hCur h), fun h => ?_⟩
  cases hI : isIdleThreadId t
  · exact hN.elsewhere e d t (Ne.symm hd) hCur hI h
  · exact absurd (hN.residentNotIdle d t h) (by rw [hI]; decide)

/-- A write to one thread's TCB changes no other thread's saved registers. -/
theorem savedRegs_updateTcb_ne {st : SystemState} {w : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) {t : SeLe4n.ThreadId} (hNe : t ≠ w) :
    (st.updateTcb w f).savedRegs t = st.savedRegs t := by
  unfold SystemState.savedRegs
  rw [SystemState.updateTcb_getTcb?_ne st w f hInv t
    (fun h => hNe (SeLe4n.ThreadId.toObjId_injective _ _ h.symm))]

/-- **A write to one thread's TCB, of a thread no other core held at `base`**,
with nothing since `base` making a thread current or resident on another
core. -/
theorem savedRegsKeptOffCore_updateTcb {e : CoreId} {base st : SystemState}
    {w : SeLe4n.ThreadId} {f : TCB → TCB} (hInv : st.objects.invExt)
    (hFree : offCoreFree e base w)
    (hK : currentKeptOffCore e base (st.updateTcb w f))
    (hR : residentKeptOffCore e base (st.updateTcb w f)) :
    savedRegsKeptOffCore e st (st.updateTcb w f) :=
  savedRegsKeptOffCore_of_writes (· = w) (fun _ hNe => savedRegs_updateTcb_ne hInv hNe)
    (fun _ h => h ▸ hFree) hK hR

/-! ### The executing core's own writes -/

/-- **The syscall's argument spill names the caller**: the FFI entry writes the
syscall's id and argument words into the caller's saved context, the executing
core's current thread, which no other core holds. -/
theorem writeFfiRegistersToTcb_savedRegsKeptOffCore {e : CoreId} {st : SystemState}
    {tid : SeLe4n.ThreadId} (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 : UInt64)
    (hInv : st.objects.invExt) (hCur : st.scheduler.currentOnCore e = some tid)
    (hU : currentsUnique st) (hN : st.currentNotResidentElsewhere) :
    savedRegsKeptOffCore e st
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) := by
  unfold Platform.FFI.writeFfiRegistersToTcb
  exact savedRegsKeptOffCore_updateTcb hInv (offCoreFree_of_current hCur hU hN)
    (currentKeptOffCore_of_eq fun _ _ => by rw [SystemState.updateTcb_scheduler])
    (residentKeptOffCore_of_eq (by rw [SystemState.updateTcb_machine]))

/-- **The caller's return staging names the caller**: it writes the thread that
was the executing core's current thread when the entry began (`base`), into
its saved context and, while it is still current, into the core's own bank.
The entry's steps since made no thread current or resident on another core, so
no other core holds the caller now either. -/
theorem stageCallerReturnFor_savedRegsKeptOffCore {e : CoreId} {base post : SystemState}
    {tid : SeLe4n.ThreadId} (o : Architecture.SyscallOutcome) (hInv : post.objects.invExt)
    (hFree : offCoreFree e base tid)
    (hK : currentKeptOffCore e base post) (hR : residentKeptOffCore e base post) :
    savedRegsKeptOffCore e post (Architecture.stageCallerReturnFor (some tid) post e o) := by
  have hW : savedRegsKeptOffCore e post (Architecture.writeReturnFrameToTcb post tid
      (match o with | .returns f => f | _ => default)) := by
    unfold Architecture.writeReturnFrameToTcb
    exact savedRegsKeptOffCore_updateTcb hInv hFree
      (currentKeptOffCore_trans hK
        (currentKeptOffCore_of_eq fun _ _ => by rw [SystemState.updateTcb_scheduler]))
      (residentKeptOffCore_trans hR
        (residentKeptOffCore_of_eq (by rw [SystemState.updateTcb_machine])))
  cases o with
  | blocks => exact savedRegsKeptOffCore_refl e post
  | faulted => exact savedRegsKeptOffCore_refl e post
  | returns f =>
    simp only [Architecture.stageCallerReturnFor]
    split
    · intro d hd t ht
      exact hW d hd t ht
    · exact hW

/-- **The scheduling point's save names the core's outgoing thread**: it writes
core `e`'s bank into the saved context of `e`'s current thread, which no other
core held at `base`. -/
theorem saveOutgoingContextOnCore_savedRegsKeptOffCore {e : CoreId} {base st : SystemState}
    (hInv : st.objects.invExt)
    (hFree : ∀ t, st.scheduler.currentOnCore e = some t → offCoreFree e base t)
    (hK : currentKeptOffCore e base st) (hR : residentKeptOffCore e base st) :
    savedRegsKeptOffCore e st (saveOutgoingContextOnCore st e) := by
  unfold saveOutgoingContextOnCore
  split
  · exact savedRegsKeptOffCore_refl e st
  · rename_i t hT
    exact savedRegsKeptOffCore_updateTcb hInv (hFree t hT)
      (currentKeptOffCore_trans hK
        (currentKeptOffCore_of_eq fun _ _ => by rw [SystemState.updateTcb_scheduler]))
      (residentKeptOffCore_trans hR
        (residentKeptOffCore_of_eq (by rw [SystemState.updateTcb_machine])))


/-! ### The yield completion's write -/

/-- **A thread linked at `base` is held by no core**: no core's current or
resident thread holds a yield link at an entry boundary
(`yieldLinkedNotResident`). -/
theorem offCoreFree_of_yieldCode {e : CoreId} {base : SystemState} {t : SeLe4n.ThreadId}
    (hY : base.yieldLinkedNotResident) (hL : (objYieldCodes base.objects[t.toObjId]?).1 ≠ 0) :
    offCoreFree e base t := fun d _ =>
  ⟨fun h => hL (objYieldCodes_fst_zero_of_getTcb? fun x hx => hY d t x (Or.inl h) hx),
   fun h => hL (objYieldCodes_fst_zero_of_getTcb? fun x hx => hY d t x (Or.inr h) hx)⟩

/-- **A context's recorded yielder is linked**: on a state whose links agree, the
thread a context names as its yielder holds a yield-to code. -/
theorem yieldCode_of_yieldFrom {st : SystemState} {s : SeLe4n.SchedContextId}
    {sc : SchedContext} {k : Nat} (hA : st.yieldLinksAgree)
    (hS : st.getSchedContext? s = some sc) (hC : sc.yieldFromCode = k + 1) :
    (objYieldCodes st.objects[(⟨k⟩ : SeLe4n.ThreadId).toObjId]?).1 ≠ 0 := by
  have h := (hA (⟨k⟩ : SeLe4n.ThreadId).toObjId s.toObjId).mpr
    (by rw [objYieldCodes_of_getSchedContext? hS]; exact hC)
  rw [h]; exact Nat.succ_ne_zero _

/-- A thread linked now was linked at `base`, when no step since set a yield-to
code (`YieldToCodesUnset`, the run-queue stage's `live` field). -/
theorem yieldCode_of_unset {st base : SystemState} {k : SeLe4n.ObjId}
    (hU : YieldToCodesUnset st base) (hL : (objYieldCodes st.objects[k]?).1 ≠ 0) :
    (objYieldCodes base.objects[k]?).1 ≠ 0 := by
  rcases hU k id with h | h
  · exact absurd h hL
  · rw [← h]; exact hL

/-- **The yield completion names a linked thread**: `completeYieldFrom` writes
the saved registers of the context's recorded yielder alone (`setConsumed`'s
consumed-time words; the link clear writes no register), a thread no other core
held at `base`. -/
theorem completeYieldFrom_savedRegsKeptOffCore {e : CoreId} {base st : SystemState}
    {s : SeLe4n.SchedContextId} (hInv : st.objects.invExt)
    (hFree : ∀ sc k, st.getSchedContext? s = some sc → sc.yieldFromCode = k + 1 →
      offCoreFree e base ⟨k⟩)
    (hK : currentKeptOffCore e base (completeYieldFrom st s))
    (hR : residentKeptOffCore e base (completeYieldFrom st s)) :
    savedRegsKeptOffCore e st (completeYieldFrom st s) := by
  revert hK hR
  unfold completeYieldFrom
  split
  · rename_i sc hS
    split
    · intro _ _; exact savedRegsKeptOffCore_refl e st
    · rename_i k hC
      intro hK hR
      refine savedRegsKeptOffCore_of_writes (· = ⟨k⟩) (fun t hNe => ?_)
        (fun _ h => h ▸ hFree sc k hS hC) hK hR
      have hInv1 := SystemState.updateSchedContext_preserves_objects_invExt st s
        SchedContext.updateConsumed hInv
      unfold setConsumed cancelYieldFrom
      simp only [hS]
      have hS1 : ((st.updateSchedContext s SchedContext.updateConsumed).updateTcb ⟨k⟩
          (TCB.withConsumed · sc.consumedReading.toUInt64)).getSchedContext? s =
          some (SchedContext.updateConsumed sc) := by
        rw [SystemState.updateTcb_getSchedContext? _ _ _ hInv1,
          SystemState.updateSchedContext_getSchedContext?_self _ _ _ hInv, hS]; rfl
      have hC1 : (SchedContext.updateConsumed sc).yieldFromCode = k + 1 := hC
      simp only [hS1, hC1]
      have hInv2 := SystemState.updateTcb_preserves_objects_invExt _ ⟨k⟩
        (TCB.withConsumed · sc.consumedReading.toUInt64) hInv1
      have hInv3 := SystemState.updateSchedContext_preserves_objects_invExt _ s
        SchedContext.yieldCleared hInv2
      rw [savedRegs_updateTcb_ne hInv3 hNe]
      unfold SystemState.savedRegs
      rw [SystemState.updateSchedContext_getTcb? _ _ _ hInv2]
      rw [show ((st.updateSchedContext s SchedContext.updateConsumed).updateTcb ⟨k⟩
          (TCB.withConsumed · sc.consumedReading.toUInt64)).getTcb? t =
          (st.updateSchedContext s SchedContext.updateConsumed).getTcb? t from
        SystemState.updateTcb_getTcb?_ne _ _ _ hInv1 t
          (fun h => hNe (SeLe4n.ThreadId.toObjId_injective _ _ h.symm)),
        SystemState.updateSchedContext_getTcb? _ _ _ hInv]
  · intro _ _; exact savedRegsKeptOffCore_refl e st


/-! ### The cancellation's write -/

/-- **The cancellation restore names the cancelled thread**: a blocking IPC
destroyed under a thread restores it to ready with the cancellation frame staged
(`restoreToReadyCancelled`), writing that thread's saved registers alone. -/
theorem restoreToReadyCancelled_savedRegsKeptOffCore {e : CoreId} {base st : SystemState}
    {tid : SeLe4n.ThreadId} (hInv : st.objects.invExt) (hFree : offCoreFree e base tid)
    (hK : currentKeptOffCore e base (Lifecycle.Suspend.restoreToReadyCancelled st tid))
    (hR : residentKeptOffCore e base (Lifecycle.Suspend.restoreToReadyCancelled st tid)) :
    savedRegsKeptOffCore e st (Lifecycle.Suspend.restoreToReadyCancelled st tid) := by
  revert hK hR
  unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
  exact savedRegsKeptOffCore_updateTcb hInv hFree

end SeLe4n.Kernel
