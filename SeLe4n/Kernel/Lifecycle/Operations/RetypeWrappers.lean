-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.ScrubAndUntyped
import SeLe4n.Kernel.Architecture.TlbShootdownProtocol
-- WS-SM SM7.F.4(b)(iii): the per-core TLB model — the retype-with-shootdown
-- wrapper additionally retires the initiator's own `perCoreTlb` view for the
-- destroyed ASID (the initiator's local `TLBI ASIDE1`, atomic with the round).
import SeLe4n.Kernel.Architecture.PerCoreTlbModel
-- WS-SM SM7.D.1: the per-core instruction-cache model — a retype re-purposes
-- the target's backing memory (it is scrubbed in the same transition), so the
-- production retype wrappers additionally broadcast `IC IALLUIS` across the
-- shareability domain.
import SeLe4n.Kernel.Architecture.PerCoreCacheModel

/-!
AN4-G.5 (LIF-M05) child module extracted from
`SeLe4n.Kernel.Lifecycle.Operations`. Contains the production retype-path
wrappers: `lifecycleRetypeWithCleanup` (composing cleanup + scrub +
retype), the `WS-K-D` syscall dispatch helpers, `lifecycleRetypeDirect`
(pre-resolved authority variant), and `lifecycleRetypeDirectWithCleanup`
(pre-resolved + safe path). These are the entry points the API dispatcher
invokes; they sit above the primitives extracted into the sibling
`Cleanup`, `CleanupPreservation`, and `ScrubAndUntyped` children.
All declarations retain their original names, order, and proofs.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)
-- AN4-A / AN4-G.5 allowlist: proof-chain reference to
-- `lifecycleRetypeObject` from `SeLe4n.Kernel.Internal`. Enforced by
-- `scripts/test_tier0_hygiene.sh`.
open Internal

-- ============================================================================
-- WS-H2/S6-C: Safe lifecycle retype wrapper (cleanup + scrub + retype)
-- ============================================================================

/-- **`v0.35.187`: what a retype requires of its replacement, in ONE place.**

Two conditions, and the second is why this predicate exists rather than a second
`if` beside the first.

* `wellFormed` — T5-D's defence in depth, with SM6.D's inert-`Reply` clause and
  `v0.35.184`'s bound-nobody `SchedContext` clause.
* **the replacement's own embedded identity is the slot it will occupy.**  A
  TCB, a SchedContext and a Reply each carry their own id in a field while the
  object store is keyed by `ObjId`, so the two can disagree —
  `PlatformConfig.wellFormed`'s `embeddedIdentitiesMatchSlots` has refused that
  at **boot** since PR #889 review round 8, and its own docstring states the
  hazard in terms: *a SchedContext at slot 9 carrying `scId = 12` would have its
  budget replenished on whatever object 12 is*.  Nothing refused it at the
  **runtime**, and `objectOfKernelType` — the one builder the live retype
  installs through — stamps the reserved **sentinel** into all three, so a
  successful retype broke at the runtime exactly the agreement the boot
  enforces.

A named predicate rather than two guards because the wrappers are the only
askers and both must ask the same question: *a named condition beside unnamed
ones is a subset*, and this tree has paid for that shape before
(`dualQueueRemovalEnabled`, `v0.35.59`).  `KernelObject.withIdentity` is what
makes it a discipline a caller can meet rather than a wall; the live dispatch
stamps with it. -/
def retypeReplacementAdmissible (newObj : KernelObject) (target : SeLe4n.ObjId)
    (objects : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject) : Prop :=
  newObj.wellFormed objects ∧ newObj.embeddedIdentityMatches target = true ∧
    newObj.objectType.memoryBacked = false

instance (newObj : KernelObject) (target : SeLe4n.ObjId)
    (objects : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject) :
    Decidable (retypeReplacementAdmissible newObj target objects) := by
  unfold retypeReplacementAdmissible; exact inferInstance

/-- **`v0.35.187`**: a stamped replacement is admissible exactly when it is
well-formed and — since WS-BP BP7.1 — of a kind that is not memory authority —
so the identity half costs a caller that stamps nothing, which is what keeps
the guard from refusing valid retypes. -/
@[simp] theorem retypeReplacementAdmissible_withIdentity (newObj : KernelObject)
    (target : SeLe4n.ObjId)
    (objects : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject) :
    retypeReplacementAdmissible (newObj.withIdentity target) target objects ↔
      newObj.wellFormed objects ∧ newObj.objectType.memoryBacked = false := by
  simp [retypeReplacementAdmissible]

/-- **`v0.35.187`**: admissibility entails well-formedness, so every existing
consumer of the T5-D guard reads it off this one. -/
theorem retypeReplacementAdmissible.wellFormed' {newObj : KernelObject}
    {target : SeLe4n.ObjId}
    {objects : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject}
    (h : retypeReplacementAdmissible newObj target objects) :
    newObj.wellFormed objects := h.1

/-- **`v0.35.187`**: and the identity agreement, which is the half the boot
check has always had and the runtime did not. -/
theorem retypeReplacementAdmissible.identity {newObj : KernelObject}
    {target : SeLe4n.ObjId}
    {objects : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject}
    (h : retypeReplacementAdmissible newObj target objects) :
    newObj.embeddedIdentityMatches target = true := h.2.1

/-- **WS-BP BP7.1**: and the replacement is not memory authority — an in-place
retype never creates an untyped region or a frame, because both would be
authority over physical memory no existing capability covered. -/
theorem retypeReplacementAdmissible.notMemoryBacked {newObj : KernelObject}
    {target : SeLe4n.ObjId}
    {objects : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject}
    (h : retypeReplacementAdmissible newObj target objects) :
    newObj.objectType.memoryBacked = false := h.2.2

/-- **`v0.36.9`: an in-place retype never creates a VSpace root.**  A root is a
translation table, which is memory (`KernelObjectType.memoryBacked`), and the
retype's own builder made one at ASID `0` — the boot VSpace root's — with no
check that the ASID was free, so `storeObject` took the ASID table's entry for
the caller's root.  Whatever its ASID, no VSpace-root replacement is admissible. -/
theorem retypeReplacementAdmissible_refuses_vspaceRoot (root : VSpaceRoot)
    (target : SeLe4n.ObjId)
    (objects : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject) :
    ¬ retypeReplacementAdmissible (.vspaceRoot root) target objects := fun h => by
  have := h.notMemoryBacked
  simp [KernelObject.objectType, KernelObjectType.memoryBacked] at this

/-- WS-H2/S6-C: Safe lifecycle retype with reference cleanup and memory scrubbing.
    Composes three phases:
    1. `lifecyclePreRetypeCleanup` — TCB scheduler dequeue + CNode CDT detach
    2. `scrubObjectMemory` — zero the backing memory of the old object (S6-C)
    3. `lifecycleRetypeObject` — replace the object in the store

    The cleanup runs on the pre-retype state; scrubbing zeros machine memory
    to prevent information leakage between security domains; the actual retype
    operates on the cleaned+scrubbed state.

    Since cleanup and scrubbing preserve `objects` and `lifecycle`, the retype
    authority check and lifecycle metadata check succeed on the scrubbed state
    iff they succeed on the original state.

    This wrapper is the recommended entry point for callers that need the
    H-05 safety guarantee and S6-C memory scrubbing guarantee.

    T5-D (M-NEW-5): Validates `KernelObject.wellFormed` for the new object before
    retype. Returns `illegalState` if the new object fails well-formedness
    (e.g., TCB with dangling cspaceRoot/vspaceRoot, CNode with out-of-range guard).
    The API layer (register decode + typed argument construction) is designed to
    produce well-formed objects, so this check is a defense-in-depth measure. -/
def lifecycleRetypeWithCleanup
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    -- T5-D: Validate the replacement before proceeding -- well-formedness,
    -- (`v0.35.187`) that its own embedded identity is the slot it will occupy,
    -- and (WS-BP BP7.1) that it is not memory authority minted from nothing.
    if ¬ retypeReplacementAdmissible newObj target st.objects then
      .error .illegalState
    else
      match st.getObject? target with
      | none => lifecycleRetypeObject authority target newObj st
      | some currentObj =>
          -- AJ1-A (M-14): Propagate cleanup errors instead of silently ignoring
          match lifecyclePreRetypeCleanup st target currentObj newObj with
          | .error e => .error e
          | .ok stClean =>
            -- S6-C: Scrub backing memory before retype to prevent info leakage
            let stScrubbed := scrubObjectMemory stClean target currentObj.objectType
            lifecycleRetypeObject authority target newObj stScrubbed

/-- WS-H2/H-05/S6-C: After a TCB retype via the safe wrapper, the old ThreadId is
    not in the run queue.  This is the key safety property required by H-05.
    The proof threads through both cleanup and scrubbing phases, using the fact
    that `scrubObjectMemory` preserves the scheduler state. -/
theorem lifecycleRetypeWithCleanup_ok_runnable_no_dangling
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (tcb : TCB)
    (hObj : st.objects[target]? = some (.tcb tcb))
    (hStep : lifecycleRetypeWithCleanup authority target newObj st = .ok ((), st')) :
    ¬(tcb.tid ∈ (st'.scheduler.runQueueOnCore bootCoreId)) := by
  unfold lifecycleRetypeWithCleanup SystemState.getObject? at hStep
  -- T5-D: wellFormed guard — since hStep is .ok, the guard must have passed
  simp only [] at hStep
  split at hStep
  · contradiction
  · rename_i hWF
    simp only [hObj] at hStep
    -- AJ1-A (M-14): lifecyclePreRetypeCleanup now returns Except; extract .ok
    cases hClean : lifecyclePreRetypeCleanup st target (.tcb tcb) newObj with
    | error e => rw [hClean] at hStep; contradiction
    | ok stClean =>
      rw [hClean] at hStep; simp only [] at hStep
      -- hStep now has lifecycleRetypeObject on the scrubbed+cleaned state
      rcases lifecycleRetypeObject_ok_as_storeObject _ st' authority target newObj hStep with
        ⟨_, _, _, _, _, _, hStore⟩
      have hSchedEq : st'.scheduler =
          (scrubObjectMemory stClean target (KernelObject.tcb tcb).objectType).scheduler :=
        lifecycle_storeObject_scheduler_eq _ st' target newObj hStore
      rw [hSchedEq, scrubObjectMemory_scheduler_eq]
      -- Extract intermediate state from lifecyclePreRetypeCleanup
      simp only [lifecyclePreRetypeCleanup] at hClean
      -- Round 39: the running-target rejection is vacuous on the `.ok` path.
      rw [if_neg (by
        intro hRun
        rw [if_pos hRun] at hClean
        exact absurd hClean (by simp))] at hClean
      -- `v0.35.164`: the pipeline's first step is the reservation arm; the sweep
      -- that follows removes the thread from the boot queue whatever that arm
      -- left, which is all this theorem reads.
      cases hArm : cancelDonationArmOnCore st tcb.tid tcb with
      | error e => rw [hArm] at hClean; simp at hClean
      | ok stArm =>
        rw [hArm] at hClean; simp only [] at hClean
        -- PR #822 review: the final `.tcb` arm rejects a TCB still holding a reply
        -- link (`.error`, vacuous on `.ok`); reduce the reject-`if` on the `.ok` path.
        have hRO : tcb.replyObject.isSome = false := by
          cases hr : tcb.replyObject.isSome with
          | false => rfl
          | true => rw [if_pos hr] at hClean; exact absurd hClean (by simp)
        rw [if_neg (by simp [hRO])] at hClean
        injection hClean with hClean; subst hClean
        -- `cleanupTcbReferences_removes_from_runnable` is polymorphic in the input
        -- state; `_` lets Lean unify it with the arm's post-state.
        exact cleanupTcbReferences_removes_from_runnable _ tcb.tid

-- ============================================================================
-- WS-K-D: Lifecycle syscall dispatch helpers
-- ============================================================================

/-- WS-K-D: Map a raw type tag and size hint to a default `KernelObject`.

Tag encoding follows `KernelObjectType` ordinal order:
- 0 = TCB, 1 = Endpoint, 2 = Notification, 3 = CNode, 4 = VSpaceRoot, 5 = Untyped,
  6 = SchedContext, 7 = Reply, 8 = Frame.

The size hint is used only for untyped objects (as `regionSize`); other types
ignore it. All constructed objects use field defaults — the retype operation
creates an identity; subsequent operations configure the object.

**AJ4-D (L-09): Sentinel-initialized placeholder IDs.** TCB reference fields
(`tid`, `cspaceRoot`, `vspaceRoot`) use the reserved sentinel value (ID 0)
from the H-06/WS-E3 convention. These IDs do not alias real kernel objects
because ID 0 is reserved system-wide. Callers MUST configure these fields
via `threadConfigureOp` before scheduling the thread. -/
def objectOfTypeTag (typeTag : Nat) (sizeHint : Nat)
    : Except KernelError KernelObject :=
  match typeTag with
  | 0 => .ok (.tcb {
      tid := SeLe4n.ThreadId.sentinel       -- AJ4-D: reserved sentinel (H-06)
      priority := SeLe4n.Priority.ofNat 0
      domain := SeLe4n.DomainId.ofNat 0
      cspaceRoot := SeLe4n.ObjId.sentinel    -- AJ4-D: reserved sentinel (H-06)
      vspaceRoot := SeLe4n.ObjId.sentinel    -- AJ4-D: reserved sentinel (H-06)
      ipcBuffer := SeLe4n.VAddr.ofNat 0
    })
  | 1 => .ok (.endpoint { sendQ := {}, receiveQ := {} })
  | 2 => .ok (.notification {
      state := .idle, waitingThreads := SeLe4n.NoDupList.empty,
      pendingBadge := none
    })
  | 3 => .ok (.cnode {
      depth := 0, guardWidth := 0, guardValue := 0,
      radixWidth := 0, slots := SeLe4n.UniqueSlotMap.empty
    })
  -- `v0.36.9`: a VSpace root built here carries ASID 0, the boot VSpace root's
  -- ASID, and the retype's admissibility guard refuses it
  -- (`KernelObjectType.memoryBacked`): a translation table is memory, carved
  -- from an untyped, never minted in place at an ASID nobody checked was free.
  | 4 => .ok (.vspaceRoot {
      asid := SeLe4n.ASID.ofNat 0, mappings := {}
    })
  | 5 => .ok (.untyped {
      regionBase := SeLe4n.PAddr.ofNat 0,
      regionSize := sizeHint,
      watermark := 0,
      children := [],
      isDevice := false
    })
  | 6 => .ok (.schedContext (SeLe4n.Kernel.SchedContext.empty SeLe4n.SchedContextId.sentinel))
  -- WS-SM SM6.D / PR #822: keep the raw Nat helper in sync with the typed
  -- `objectOfKernelType` + `KernelObjectType.ofNat?` + the Rust ABI (tags 0–7,
  -- including SchedContext = 6 and the first-class Reply = 7).
  | 7 => .ok (.reply (SeLe4n.Kernel.Reply.empty SeLe4n.ReplyId.sentinel))
  -- WS-BP BP7.1: tag 8 is a frame.  Built at physical address 0 — a value the
  -- retype's admissibility guard refuses (`KernelObjectType.memoryBacked`), since
  -- a frame is carved from an untyped and never minted in place.
  | 8 => .ok (.frame { base := SeLe4n.PAddr.ofNat 0 })
  -- WS-BP BP7.1 (`v0.36.12`): tag 9 is a page table, refused in place the same way.
  | 9 => .ok (.pageTable { base := SeLe4n.PAddr.ofNat 0 })
  | _ + 10 => .error .invalidTypeTag

/-- R7-E/L-10: Typed version of `objectOfTypeTag` that takes `KernelObjectType` directly.
    Eliminates the invalid-tag error path since the type is already validated.

    **AJ4-D (L-09):** Same sentinel-initialization convention as `objectOfTypeTag`.
    See that function's docstring for the H-06/WS-E3 sentinel rationale. -/
def objectOfKernelType (objType : KernelObjectType) (sizeHint : Nat) : KernelObject :=
  match objType with
  | .tcb => .tcb {
      tid := SeLe4n.ThreadId.sentinel       -- AJ4-D: reserved sentinel (H-06)
      priority := SeLe4n.Priority.ofNat 0
      domain := SeLe4n.DomainId.ofNat 0
      cspaceRoot := SeLe4n.ObjId.sentinel    -- AJ4-D: reserved sentinel (H-06)
      vspaceRoot := SeLe4n.ObjId.sentinel    -- AJ4-D: reserved sentinel (H-06)
      ipcBuffer := SeLe4n.VAddr.ofNat 0
    }
  | .endpoint => .endpoint { sendQ := {}, receiveQ := {} }
  | .notification => .notification {
      state := .idle, waitingThreads := SeLe4n.NoDupList.empty,
      pendingBadge := none
    }
  | .cnode => .cnode {
      depth := 0, guardWidth := 0, guardValue := 0,
      radixWidth := 0, slots := SeLe4n.UniqueSlotMap.empty
    }
  | .vspaceRoot => .vspaceRoot {
      asid := SeLe4n.ASID.ofNat 0, mappings := {}
    }
  | .untyped => .untyped {
      regionBase := SeLe4n.PAddr.ofNat 0,
      regionSize := sizeHint,
      watermark := 0,
      children := [],
      isDevice := false
    }
  | .schedContext => .schedContext (SeLe4n.Kernel.SchedContext.empty SeLe4n.SchedContextId.sentinel)
  | .reply => .reply (SeLe4n.Kernel.Reply.empty SeLe4n.ReplyId.sentinel)
  -- WS-BP BP7.1: see `objectOfTypeTag`'s tag 8 — refused by the admissibility
  -- guard, which is what keeps this placeholder address from ever being stored.
  | .frame => .frame { base := SeLe4n.PAddr.ofNat 0 }
  -- WS-BP BP7.1 (`v0.36.12`): the same, for a page table.
  | .pageTable => .pageTable { base := SeLe4n.PAddr.ofNat 0 }

-- ============================================================================
-- WS-K-D: lifecycleRetypeDirect — pre-resolved authority variant
-- ============================================================================

/-- **Internal building block — callers should use `lifecycleRetypeDirectWithCleanup` instead.**

WS-K-D: Retype with a pre-resolved authority capability.
Companion to `lifecycleRetypeObject` for the register-sourced dispatch
path where the authority cap has already been resolved by `syscallInvoke`.

T5-B (M-NEW-4): Marked as internal. This function takes a pre-resolved
`Capability` and bypasses cleanup and memory scrubbing. External callers
must use `lifecycleRetypeDirectWithCleanup` (for pre-resolved caps) or
`lifecycleRetypeWithCleanup` (for CSpaceAddr) for the H-05 and S6-C
guarantees. U-H04: API dispatch now routes through the safe wrapper.

V5-B (M-DEF-2): **Internal only — do not call from new code.**
See `lifecycleRetypeObject` for the full rationale.

Deterministic branch contract:
1. Target object must exist (`objectNotFound` otherwise).
2. Lifecycle metadata must agree with object-store type (`illegalState`).
3. Authority cap must satisfy `lifecycleRetypeAuthority` — targets the
   object with `.retype` right (`illegalAuthority` otherwise).
4. Object store is updated atomically on success via `storeObject`. -/
def lifecycleRetypeDirect
    (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    match st.getObject? target with
    | none => .error .objectNotFound
    | some currentObj =>
        if st.lifecycle.objectTypes[target]? = some currentObj.objectType then
          if lifecycleRetypeAuthority authCap target then
            storeObject target newObj st
          else
            .error .illegalAuthority
        else
          .error .illegalState

/-- **`v0.35.185` (register row 63): the direct retype IS a `storeObject`, under
two guards that commit nothing.**

`lifecycleRetypeObject_ok_as_storeObject`'s sibling for the pre-resolved variant
— the same decomposition, at a `Capability` rather than a `CSpaceAddr`, so a
consumer reasoning about what the retype writes has one step to reason about.

Stated because the retype composite's invariant theorems need exactly this: every
object-level fact about the destroy path's last step is a fact about
`storeObject`. -/
theorem lifecycleRetypeDirect_ok_as_storeObject
    (st st' : SystemState) (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (h : lifecycleRetypeDirect authCap target newObj st = .ok ((), st')) :
    storeObject target newObj st = .ok ((), st') := by
  unfold lifecycleRetypeDirect SystemState.getObject? at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · split at h
      · exact h
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- **WS-RR RR8.12 Cut C6g**: the direct retype is scheduler- and machine-silent —
it is a `storeObject` under two guards, and the guards commit nothing.

Declared here, beside the step, rather than as the `private` copy that lived in the
staged non-interference module: a production consumer (the retype footprint's
replenish exactness frame) needs it, and a private theorem in a staged module is
one no production asker can reach. -/
theorem lifecycleRetypeDirect_scheduler_machine_eq
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st st' : SystemState)
    (h : lifecycleRetypeDirect authCap target newObj st = .ok ((), st')) :
    st'.scheduler = st.scheduler ∧ st'.machine = st.machine := by
  unfold lifecycleRetypeDirect SystemState.getObject? at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · split at h
      · exact ⟨storeObject_scheduler_eq st st' target newObj h,
              storeObject_machine_eq st st' target newObj h⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)

-- ============================================================================
-- U-H04: lifecycleRetypeDirectWithCleanup — pre-resolved authority + safe path
-- ============================================================================

/-- U-H04: Safe lifecycle retype with pre-resolved authority capability.

Combines `lifecycleRetypeDirect`'s pre-resolved cap dispatch with the
cleanup and memory scrubbing guarantees of `lifecycleRetypeWithCleanup`.
This is the correct entry point for API dispatch, which resolves the
authority cap before entering the retype arm.

Phases:
1. Well-formedness validation (T5-D defense-in-depth)
2. `lifecyclePreRetypeCleanup` — TCB scheduler dequeue + CNode CDT detach
3. `scrubObjectMemory` — zero backing memory (S6-C security guarantee)
4. `lifecycleRetypeDirect` — replace object in store with authority check -/
def lifecycleRetypeDirectWithCleanup
    (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    -- T5-D: Validate the replacement before proceeding -- well-formedness,
    -- (`v0.35.187`) that its own embedded identity is the slot it will occupy,
    -- and (WS-BP BP7.1) that it is not memory authority minted from nothing.
    if ¬ retypeReplacementAdmissible newObj target st.objects then
      .error .illegalState
    else
      match st.getObject? target with
      | none => lifecycleRetypeDirect authCap target newObj st
      | some currentObj =>
          -- AJ1-A (M-14): Propagate cleanup errors instead of silently ignoring
          match lifecyclePreRetypeCleanup st target currentObj newObj with
          | .error e => .error e
          | .ok stClean =>
            let stScrubbed := scrubObjectMemory stClean target currentObj.objectType
            lifecycleRetypeDirect authCap target newObj stScrubbed

/-- **`v0.35.185` (register row 63): what a successful cleanup-composed retype
did**, in one place.

Three facts, and the composite's invariant theorems each need all three: the
replacement was **admissible** (which is what makes `v0.35.184`'s `.schedContext`
clause and `v0.35.187`'s identity clause *runtime refusals* rather than caller
obligations), the target held some object the cleanup ran on, and the whole of
the commit is one `storeObject` on the scrubbed post-cleanup state.

The `none` arm of the wrapper's own `getObject?` match is unreachable on `.ok`,
because `lifecycleRetypeDirect` re-asks the same question and answers
`.objectNotFound` — so the existential is total on the success path rather than
a case the caller must still split.

Stated once because two invariant theorems (`…_preserves_schedContextBindingConsistent`
and `…_preserves_replenishQueueAffinityConsistent_smp`) had the same twenty-line
decomposition inlined, and a second reading of what a transition does is the
duplication this project treats as debt.
`lifecycleRetypeDirectWithCleanup_vspaceRoot_storeObject` is this fact
specialised to a `.vspaceRoot` current object, where the cleanup is the
identity. -/
theorem lifecycleRetypeDirectWithCleanup_ok_decompose
    {st st' : SystemState} {authCap : Capability} {target : SeLe4n.ObjId}
    {newObj : KernelObject}
    (h : lifecycleRetypeDirectWithCleanup authCap target newObj st = .ok ((), st')) :
    retypeReplacementAdmissible newObj target st.objects ∧
      ∃ currentObj stClean,
        st.objects[target]? = some currentObj ∧
        lifecyclePreRetypeCleanup st target currentObj newObj = .ok stClean ∧
        storeObject target newObj
            (scrubObjectMemory stClean target currentObj.objectType) = .ok ((), st') := by
  unfold lifecycleRetypeDirectWithCleanup SystemState.getObject? at h
  split at h
  · exact absurd h (by simp)
  · rename_i hWF
    refine ⟨by simpa using hWF, ?_⟩
    cases hCur : st.objects[target]? with
    | none =>
      -- Unreachable: the direct retype re-asks and answers `.objectNotFound`.
      rw [hCur] at h
      unfold lifecycleRetypeDirect SystemState.getObject? at h
      rw [hCur] at h
      exact absurd h (by simp)
    | some currentObj =>
      rw [hCur] at h
      simp only [] at h
      cases hClean : lifecyclePreRetypeCleanup st target currentObj newObj with
      | error e => rw [hClean] at h; exact absurd h (by simp)
      | ok stClean =>
        rw [hClean] at h
        simp only [] at h
        exact ⟨currentObj, stClean, rfl, hClean,
          lifecycleRetypeDirect_ok_as_storeObject _ st' authCap target newObj h⟩

-- ============================================================================
-- WS-SM SM7.B.11 / SM7.F.4(b)(iii): the ASID set a retype owes the TLB
--
-- `Model.storeObject` of a `.vspaceRoot newRoot` runs
-- `asidTable.insert newRoot.asid target` — it **rebinds** `newRoot.asid`.
-- So a retype must flush TWO ASIDs, not one:
--   * the **destroyed** ASID (the old `.vspaceRoot` at `target`) — its whole
--     address space dies with the retype; and
--   * the **installed** ASID (`newRoot.asid`, when the new object is a
--     `.vspaceRoot`) — the `asidTable.insert` rebinds it to `target`, so any
--     core caching an entry for it (pointing at the *prior* binding) is now
--     stale.  (Reachable: root A asid 0, map+cache asid 0, retype root B asid 0
--     from Untyped ⇒ rebinds asid 0, leaving A's cached asid-0 entries
--     stale-and-uncovered.)
-- Both wrappers post a `.aside1` shootdown round for **each** ASID in this set
-- (deduplicated: when the destroyed and installed ASIDs coincide the set holds
-- one).  Non-VSpaceRoot retypes into non-VSpaceRoot objects owe nothing (the
-- set is empty).
-- ============================================================================

/-- **WS-SM SM7.F.4(b)(iii)**: the ASID the newly-installed object rebinds — a
`.vspaceRoot`'s ASID (which `storeObject` inserts into `asidTable`), else none. -/
def retypeInstalledAsid : KernelObject → Option SeLe4n.ASID
  | .vspaceRoot nr => some nr.asid
  | _ => none

/-- **WS-SM SM7.F.4(b)(iii)**: the ASID whose address space a retype of `target`
destroys — the old `.vspaceRoot` at `target`'s, read from the pre-state through
the AN10-B typed accessor (`getVSpaceRoot?`), never the raw store.  The
destroyed-side companion of `retypeInstalledAsid`. -/
def retypeDestroyedAsid (st : SystemState) (target : SeLe4n.ObjId) : Option SeLe4n.ASID :=
  (st.getVSpaceRoot? target).map (·.asid)

/-- **WS-SM SM7.F.4(b)(iii)**: the ASID set a retype of `target` into `newObj`
owes the TLB — the destroyed ASID (`retypeDestroyedAsid`, the old `.vspaceRoot`
at `target`) together with the installed ASID (`retypeInstalledAsid`, `newObj`'s
when a `.vspaceRoot`), manually deduplicated so an in-place ASID reuse flushes
once. -/
def retypeShootdownAsidList (st : SystemState) (target : SeLe4n.ObjId)
    (newObj : KernelObject) : List SeLe4n.ASID :=
  match retypeDestroyedAsid st target, retypeInstalledAsid newObj with
  | none, none => []
  | some a, none => [a]
  | none, some b => [b]
  | some a, some b => if a = b then [a] else [a, b]

/-- **WS-SM SM7.F.4(b)(iii)**: post one `.aside1` shootdown round per ASID in the
retype's flush set, threading state left-to-right.  Total and fail-closed: each
`tlbFlushByASIDWithShootdown` is itself total (`.ok`), and any `.error` would
propagate.  Shared by both production retype-with-shootdown wrappers. -/
def retypeShootdownAsids (executingCore : SeLe4n.Kernel.Concurrency.CoreId) :
    List SeLe4n.ASID → Kernel Unit
  | [], st => .ok ((), st)
  | a :: rest, st =>
      match Architecture.tlbFlushByASIDWithShootdown executingCore a st with
      | .error e => .error e
      | .ok ((), st') => retypeShootdownAsids executingCore rest st'

/-- **WS-SM SM7.F.4(b)(iii)** (the pure per-ASID step behind `retypeShootdownAsids`):
one `tlbFlushByASIDWithShootdown` — local scalar `TLBI ASIDE1` then the coalescing
`.aside1` round to the remote targets. -/
def retypeAsidRoundStep (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (a : SeLe4n.ASID) (s : SystemState) : SystemState :=
  Architecture.tlbShootdownBroadcastCoalescing
    { s with tlb := adapterFlushTlbByAsid s.tlb a }
    executingCore (Architecture.shootdownTargets executingCore)
    (Architecture.encodeAsidInvalidation a)

/-- **WS-SM SM7.F.4(b)(iii)** (the pure state `retypeShootdownAsids` commits): the
left-fold of `retypeAsidRoundStep` over the flush set. -/
def retypeAsidRoundFold (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (asids : List SeLe4n.ASID) (s : SystemState) : SystemState :=
  asids.foldl (fun st a => retypeAsidRoundStep executingCore a st) s

/-- **WS-SM SM7.F.4(b)(iii)** (the shootdown-state projection of the round fold):
the fold of coalescing round postings, one per flushed ASID. -/
def roundFoldSd (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (asids : List SeLe4n.ASID)
    (sd : Architecture.TlbShootdownState) :
    Architecture.TlbShootdownState :=
  asids.foldl (fun s a => Architecture.postShootdownRoundCoalescing s executingCore
    (Architecture.shootdownTargets executingCore)
    (Architecture.encodeAsidInvalidation a)) sd

-- ----------------------------------------------------------------------------
-- WS-SM SM7.F.4(b)(iii): pure closed forms + framing for the round fold
-- ----------------------------------------------------------------------------

/-- **WS-SM SM7.F.4(b)(iii)**: `tlbFlushByASIDWithShootdown` commits exactly the
pure `retypeAsidRoundStep`. -/
theorem tlbFlushByASIDWithShootdown_eq_step
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (a : SeLe4n.ASID)
    (s : SystemState) :
    Architecture.tlbFlushByASIDWithShootdown executingCore a s
      = .ok ((), retypeAsidRoundStep executingCore a s) := by
  unfold Architecture.tlbFlushByASIDWithShootdown Architecture.tlbFlushByASID
  simp only []
  rw [Architecture.withShootdownRound_total]
  rfl

/-- **WS-SM SM7.F.4(b)(iii)**: `retypeShootdownAsids` commits exactly the pure
`retypeAsidRoundFold`. -/
theorem retypeShootdownAsids_eq
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (asids : List SeLe4n.ASID)
    (s : SystemState) :
    retypeShootdownAsids executingCore asids s
      = .ok ((), retypeAsidRoundFold executingCore asids s) := by
  induction asids generalizing s with
  | nil => rfl
  | cons a rest ih =>
      have hstep : retypeAsidRoundFold executingCore (a :: rest) s
        = retypeAsidRoundFold executingCore rest (retypeAsidRoundStep executingCore a s) := rfl
      simp only [retypeShootdownAsids, tlbFlushByASIDWithShootdown_eq_step]
      rw [ih, hstep]

/-- **WS-SM SM7.F.4(b)(iii)**: the round step frames the object store. -/
theorem retypeAsidRoundStep_objects
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (a : SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundStep executingCore a s).objects = s.objects := by
  unfold retypeAsidRoundStep
  rw [(Architecture.tlbShootdownBroadcastCoalescing_frame _ _ _ _).1]

/-- **WS-SM SM8.B.2**: the round step frames the scheduler.

TLB maintenance is not scheduling: the step writes the scalar `tlb` and posts to
`tlbShootdown`, and neither is a per-core observable slot. -/
theorem retypeAsidRoundStep_scheduler
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (a : SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundStep executingCore a s).scheduler = s.scheduler := by
  unfold retypeAsidRoundStep
  rw [(Architecture.tlbShootdownBroadcastCoalescing_frame _ _ _ _).2.1]

/-- **WS-SM SM8.B.2**: the round step frames the machine, register banks
included. -/
theorem retypeAsidRoundStep_machine
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (a : SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundStep executingCore a s).machine = s.machine := by
  unfold retypeAsidRoundStep
  rw [(Architecture.tlbShootdownBroadcastCoalescing_frame _ _ _ _).2.2.1]

/-- **WS-SM SM7.F.4(b)(iii)**: the round step frames the ASID table. -/
theorem retypeAsidRoundStep_asidTable
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (a : SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundStep executingCore a s).asidTable = s.asidTable := rfl

/-- **WS-SM SM7.F.4(b)(iii)**: the round step frames the per-core TLB. -/
theorem retypeAsidRoundStep_perCoreTlb
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (a : SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundStep executingCore a s).perCoreTlb = s.perCoreTlb := rfl

/-- **WS-SM SM7.F.4(b)(iii)**: the round step's shootdown effect is the coalescing
round posting. -/
theorem retypeAsidRoundStep_tlbShootdown
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (a : SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundStep executingCore a s).tlbShootdown =
      Architecture.postShootdownRoundCoalescing s.tlbShootdown executingCore
        (Architecture.shootdownTargets executingCore)
        (Architecture.encodeAsidInvalidation a) := rfl

/-- **WS-SM SM7.F.4(b)(iii)**: the round fold frames the object store. -/
theorem retypeAsidRoundFold_objects
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (asids : List SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundFold executingCore asids s).objects = s.objects := by
  induction asids generalizing s with
  | nil => rfl
  | cons a rest ih =>
      have h1 : retypeAsidRoundFold executingCore (a :: rest) s
        = retypeAsidRoundFold executingCore rest (retypeAsidRoundStep executingCore a s) := rfl
      rw [h1, ih, retypeAsidRoundStep_objects]

/-- **WS-SM SM8.B.2**: the round fold frames the scheduler — one round per
flushed ASID, none of them scheduling. -/
theorem retypeAsidRoundFold_scheduler
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (asids : List SeLe4n.ASID)
    (s : SystemState) :
    (retypeAsidRoundFold executingCore asids s).scheduler = s.scheduler := by
  induction asids generalizing s with
  | nil => rfl
  | cons a rest ih =>
      have h1 : retypeAsidRoundFold executingCore (a :: rest) s
        = retypeAsidRoundFold executingCore rest (retypeAsidRoundStep executingCore a s) := rfl
      rw [h1, ih, retypeAsidRoundStep_scheduler]

/-- **WS-SM SM8.B.2**: the round fold frames the machine. -/
theorem retypeAsidRoundFold_machine
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (asids : List SeLe4n.ASID)
    (s : SystemState) :
    (retypeAsidRoundFold executingCore asids s).machine = s.machine := by
  induction asids generalizing s with
  | nil => rfl
  | cons a rest ih =>
      have h1 : retypeAsidRoundFold executingCore (a :: rest) s
        = retypeAsidRoundFold executingCore rest (retypeAsidRoundStep executingCore a s) := rfl
      rw [h1, ih, retypeAsidRoundStep_machine]

/-- **WS-SM SM7.F.4(b)(iii)**: the round fold frames the ASID table. -/
theorem retypeAsidRoundFold_asidTable
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (asids : List SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundFold executingCore asids s).asidTable = s.asidTable := by
  induction asids generalizing s with
  | nil => rfl
  | cons a rest ih =>
      have h1 : retypeAsidRoundFold executingCore (a :: rest) s
        = retypeAsidRoundFold executingCore rest (retypeAsidRoundStep executingCore a s) := rfl
      rw [h1, ih, retypeAsidRoundStep_asidTable]

/-- **WS-SM SM7.F.4(b)(iii)**: the round fold frames the per-core TLB. -/
theorem retypeAsidRoundFold_perCoreTlb
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (asids : List SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundFold executingCore asids s).perCoreTlb = s.perCoreTlb := by
  induction asids generalizing s with
  | nil => rfl
  | cons a rest ih =>
      have h1 : retypeAsidRoundFold executingCore (a :: rest) s
        = retypeAsidRoundFold executingCore rest (retypeAsidRoundStep executingCore a s) := rfl
      rw [h1, ih, retypeAsidRoundStep_perCoreTlb]

/-- **WS-SM SM7.F.4(b)(iii)**: the round fold's shootdown effect is the coalescing
round-posting fold. -/
theorem retypeAsidRoundFold_tlbShootdown
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (asids : List SeLe4n.ASID) (s : SystemState) :
    (retypeAsidRoundFold executingCore asids s).tlbShootdown =
      roundFoldSd executingCore asids s.tlbShootdown := by
  induction asids generalizing s with
  | nil => rfl
  | cons a rest ih =>
      have h1 : retypeAsidRoundFold executingCore (a :: rest) s
        = retypeAsidRoundFold executingCore rest (retypeAsidRoundStep executingCore a s) := rfl
      have h2 : roundFoldSd executingCore (a :: rest) s.tlbShootdown
        = roundFoldSd executingCore rest
            (Architecture.postShootdownRoundCoalescing s.tlbShootdown executingCore
              (Architecture.shootdownTargets executingCore)
              (Architecture.encodeAsidInvalidation a)) := rfl
      rw [h1, ih, retypeAsidRoundStep_tlbShootdown, h2]

/-- **WS-SM SM7.F.4(b)(iii)**: the round-posting fold preserves the capacity
invariant. -/
theorem roundFoldSd_preserves_pendingBounded
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (asids : List SeLe4n.ASID)
    {sd : Architecture.TlbShootdownState}
    (hB : Architecture.pendingBounded sd) :
    Architecture.pendingBounded (roundFoldSd executingCore asids sd) := by
  induction asids generalizing sd with
  | nil => exact hB
  | cons a rest ih =>
      have h1 : roundFoldSd executingCore (a :: rest) sd
        = roundFoldSd executingCore rest
            (Architecture.postShootdownRoundCoalescing sd executingCore
              (Architecture.shootdownTargets executingCore)
              (Architecture.encodeAsidInvalidation a)) := rfl
      rw [h1]
      exact ih (Architecture.postShootdownRoundCoalescing_preserves_pendingBounded hB _ _ _)

-- ----------------------------------------------------------------------------
-- WS-SM SM7.F.4(b)(iii): multi-round coverage survival
--
-- A retype posts one round per flushed ASID.  For a remote core `c`, a stale
-- entry `e` whose ASID is flushed rides a *pending* descriptor — but the round
-- that posts it is followed by the remaining rounds, so its coverage must
-- *survive* those.  Posting is additive (`enqueueShootdownOrCoalesce` appends,
-- or coalesces to a superseding `.vmalle1`) and `beginShootdownRoundFor` never
-- drops a pending descriptor, so coverage is monotone under further round
-- postings.
-- ----------------------------------------------------------------------------

/-- **WS-SM SM7.F.4(b)(iii)**: a descriptor pending before the coalescing posting
fold is still pending after it, or a superseding `.vmalle1` is (target set
`Nodup`). -/
private theorem foldl_coalesce_pending_covered :
    ∀ (targets : List SeLe4n.Kernel.Concurrency.CoreId)
      (dNew : Architecture.TlbShootdownDescriptor), targets.Nodup →
    ∀ (sd : Architecture.TlbShootdownState) (c : SeLe4n.Kernel.Concurrency.CoreId)
      (dOld : Architecture.TlbShootdownDescriptor),
      dOld ∈ sd.pendingOnCore c →
      dOld ∈ (targets.foldl (fun s c' => Architecture.enqueueShootdownOrCoalesce s c' dNew)
          sd).pendingOnCore c ∨
      ∃ d' ∈ (targets.foldl (fun s c' => Architecture.enqueueShootdownOrCoalesce s c' dNew)
          sd).pendingOnCore c, d'.op = Architecture.TlbInvalidation.vmalle1 := by
  intro targets
  induction targets with
  | nil => intro dNew _ sd c dOld h; exact Or.inl h
  | cons t ts ih =>
    intro dNew hnd sd c dOld h
    rw [List.foldl_cons]
    by_cases hct : c = t
    · subst hct
      rw [Architecture.foldl_enqueueShootdownOrCoalesce_frame_pending ts _ _
          (List.nodup_cons.mp hnd).1]
      exact Architecture.enqueueShootdownOrCoalesce_pending_covered sd c dNew dOld h
    · have h' : dOld ∈ (Architecture.enqueueShootdownOrCoalesce sd t dNew).pendingOnCore c := by
        rw [Architecture.enqueueShootdownOrCoalesce_frame_pending sd hct dNew]; exact h
      exact ih dNew (List.nodup_cons.mp hnd).2 _ c dOld h'

/-- **WS-SM SM7.F.4(b)(iii)**: entry coverage on a core survives one further
round posting. -/
private theorem covers_survives_one_round
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (op : Architecture.TlbInvalidation)
    (sd : Architecture.TlbShootdownState) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (dsc : Architecture.TlbShootdownDescriptor)
    (h : dsc ∈ sd.pendingOnCore c ∨
      ∃ d' ∈ sd.pendingOnCore c, d'.op = Architecture.TlbInvalidation.vmalle1) :
    dsc ∈ (Architecture.postShootdownRoundCoalescing sd executingCore
        (Architecture.shootdownTargets executingCore) op).pendingOnCore c ∨
    ∃ d' ∈ (Architecture.postShootdownRoundCoalescing sd executingCore
        (Architecture.shootdownTargets executingCore) op).pendingOnCore c,
      d'.op = Architecture.TlbInvalidation.vmalle1 := by
  unfold Architecture.postShootdownRoundCoalescing
  rcases h with hin | ⟨d', hd'in, hd'op⟩
  · have hbegin : dsc ∈
        (Architecture.beginShootdownRoundFor sd executingCore
          (Architecture.shootdownTargets executingCore)).pendingOnCore c := by
      rw [Architecture.beginShootdownRoundFor_frame_pending]; exact hin
    exact foldl_coalesce_pending_covered _ _ (Architecture.shootdownTargets_nodup executingCore)
      _ c dsc hbegin
  · have hbegin : d' ∈
        (Architecture.beginShootdownRoundFor sd executingCore
          (Architecture.shootdownTargets executingCore)).pendingOnCore c := by
      rw [Architecture.beginShootdownRoundFor_frame_pending]; exact hd'in
    rcases foldl_coalesce_pending_covered _ _ (Architecture.shootdownTargets_nodup executingCore)
        _ c d' hbegin with hsurv | ⟨d'', hd''in, hd''op⟩
    · exact Or.inr ⟨d', hsurv, hd'op⟩
    · exact Or.inr ⟨d'', hd''in, hd''op⟩

/-- **WS-SM SM7.F.4(b)(iii)**: entry coverage survives the whole round-posting
fold. -/
private theorem covers_survives_roundFold
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (asids : List SeLe4n.ASID) :
    ∀ (sd : Architecture.TlbShootdownState) (c : SeLe4n.Kernel.Concurrency.CoreId)
      (dsc : Architecture.TlbShootdownDescriptor),
      (dsc ∈ sd.pendingOnCore c ∨
        ∃ d' ∈ sd.pendingOnCore c, d'.op = Architecture.TlbInvalidation.vmalle1) →
      dsc ∈ (roundFoldSd executingCore asids sd).pendingOnCore c ∨
      ∃ d' ∈ (roundFoldSd executingCore asids sd).pendingOnCore c,
        d'.op = Architecture.TlbInvalidation.vmalle1 := by
  induction asids with
  | nil => intro sd c dsc h; exact h
  | cons a rest ih =>
    intro sd c dsc h
    have hstep : roundFoldSd executingCore (a :: rest) sd
      = roundFoldSd executingCore rest
          (Architecture.postShootdownRoundCoalescing sd executingCore
            (Architecture.shootdownTargets executingCore)
            (Architecture.encodeAsidInvalidation a)) := rfl
    rw [hstep]
    exact ih _ c dsc (covers_survives_one_round executingCore
      (Architecture.encodeAsidInvalidation a) sd c dsc h)

/-- **WS-SM SM7.F.4(b)(iii)**: after the round fold, every remote target's queue
covers each flushed ASID — the round that posts `encode a` runs, and its
coverage survives the remaining rounds.

Stated as "*some* pending descriptor carries the ASID's operand or a full
flush" rather than naming a concrete descriptor: since SM7.F.3 a descriptor
also carries its round's generation, and in a multi-ASID fold each round
mints its own, so the covering descriptor's identity is fold-position
dependent while its *operand* — the only thing coverage depends on — is
not. -/
private theorem roundFoldSd_covers
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    {c : SeLe4n.Kernel.Concurrency.CoreId}
    (hc : c ∈ Architecture.shootdownTargets executingCore) :
    ∀ (asids : List SeLe4n.ASID) (a : SeLe4n.ASID), a ∈ asids →
    ∀ (sd : Architecture.TlbShootdownState),
      ∃ d ∈ (roundFoldSd executingCore asids sd).pendingOnCore c,
        d.op = Architecture.encodeAsidInvalidation a ∨
          d.op = Architecture.TlbInvalidation.vmalle1 := by
  intro asids
  induction asids with
  | nil => intro a ha; simp at ha
  | cons x rest ih =>
    intro a ha sd
    rcases List.mem_cons.mp ha with hax | hax
    · cases hax
      have hstep : roundFoldSd executingCore (x :: rest) sd
        = roundFoldSd executingCore rest
            (Architecture.postShootdownRoundCoalescing sd executingCore
              (Architecture.shootdownTargets executingCore)
              (Architecture.encodeAsidInvalidation x)) := rfl
      rw [hstep]
      rcases covers_survives_roundFold executingCore rest _ c _
          (Architecture.postShootdownRoundCoalescing_covered sd executingCore
            (Architecture.shootdownTargets_nodup executingCore)
            (Architecture.encodeAsidInvalidation x) c hc) with hdirect | ⟨d', hd', hop'⟩
      · exact ⟨_, hdirect, Or.inl rfl⟩
      · exact ⟨d', hd', Or.inr hop'⟩
    · have hstep : roundFoldSd executingCore (x :: rest) sd
        = roundFoldSd executingCore rest
            (Architecture.postShootdownRoundCoalescing sd executingCore
              (Architecture.shootdownTargets executingCore)
              (Architecture.encodeAsidInvalidation x)) := rfl
      rw [hstep]
      exact ih a hax _

-- ----------------------------------------------------------------------------
-- WS-SM SM7.F.4(b)(iii): the flush-set membership lemmas
-- ----------------------------------------------------------------------------

/-- **WS-SM SM7.F.4(b)(iii)**: the destroyed-ASID accessor resolves to the live
root's ASID (the typed-accessor characterization of `retypeDestroyedAsid`). -/
theorem retypeDestroyedAsid_of_root
    {st : SystemState} {target : SeLe4n.ObjId} {root : VSpaceRoot}
    (hGV : st.getVSpaceRoot? target = some root) :
    retypeDestroyedAsid st target = some root.asid := by
  simp only [retypeDestroyedAsid, hGV, Option.map_some]

/-- **WS-SM SM7.F.4(b)(iii)**: the destroyed ASID is in the flush set. -/
theorem retypeShootdownAsidList_mem_destroyed
    {st : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject} {root : VSpaceRoot}
    (hGV : st.getVSpaceRoot? target = some root) :
    root.asid ∈ retypeShootdownAsidList st target newObj := by
  unfold retypeShootdownAsidList
  rw [retypeDestroyedAsid_of_root hGV]
  cases retypeInstalledAsid newObj with
  | none => simp
  | some b =>
      by_cases hb : root.asid = b
      · simp [hb]
      · simp [hb]

/-- **WS-SM SM7.F.4(b)(iii)**: neither ASID present ⇒ empty flush set (the
non-VSpaceRoot-into-non-VSpaceRoot case owes no TLB work). -/
theorem retypeShootdownAsidList_nil
    {st : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hOld : st.getVSpaceRoot? target = none)
    (hNew : retypeInstalledAsid newObj = none) :
    retypeShootdownAsidList st target newObj = [] := by
  simp only [retypeShootdownAsidList, retypeDestroyedAsid, hOld, Option.map_none, hNew]

-- ============================================================================
-- WS-SM SM7.B.11: retype-with-page-free shootdown
-- ============================================================================

/-- **WS-SM SM7.B.11**: **production entry point** — pre-resolved-cap
retype with cleanup, scrub, and TLB shootdown.

`lifecycleRetypeDirectWithCleanup` dequeues, detaches, scrubs, and
replaces the object — but until SM7.B it performed **no TLB
maintenance**: retyping a live `.vspaceRoot` freed every page mapping
the root held while every core (including the executing one) could
still translate through cached entries for its ASID — a
use-after-free of the whole address space, the retype instance of the
SMP-C4 hazard.  This wrapper closes it: when the retyped object was a
`.vspaceRoot`, the destroyed ASID is flushed locally
(`adapterFlushTlbByAsid`) and a `.aside1` shootdown round is posted to
every other core.  **The installed ASID is flushed too** (SM7.F.4(b)(iii)):
`Model.storeObject` of a `.vspaceRoot newRoot` runs
`asidTable.insert newRoot.asid target`, **rebinding** `newRoot.asid`; any core
caching an entry for it (pointing at the prior binding) is now stale, so the
wrapper posts a round for each ASID in `retypeShootdownAsidList` — the destroyed
ASID *and* the installed one (deduplicated).  Non-VSpaceRoot retypes into
non-VSpaceRoot objects owe no TLB work and commit exactly the base operation's
state. -/
def lifecycleRetypeDirectWithCleanupShootdown (executingCore :
      SeLe4n.Kernel.Concurrency.CoreId)
    (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    match lifecycleRetypeDirectWithCleanup authCap target newObj st with
    | .error e => .error e
    | .ok ((), st') =>
        -- the ASIDs a retype owes the TLB (read the destroyed one from the
        -- pre-state through the AN10-B typed accessor `getVSpaceRoot?`, never
        -- the raw store): retyping a live `.vspaceRoot` destroys an entire
        -- address space at once (every mapping the root held dies with it) AND
        -- installing a fresh `.vspaceRoot` rebinds its ASID.  Both are flushed
        -- on every core (post one `.aside1` round per ASID); a non-VSpaceRoot
        -- retype into a non-VSpaceRoot object frees no mapped pages, rebinds no
        -- ASID, and owes nothing (the flush set is empty).
        retypeShootdownAsids executingCore (retypeShootdownAsidList st target newObj) st'

/-- **WS-SM SM7.B.11 / SM7.F.4(b)(iii)**: a non-VSpaceRoot retype into a
non-VSpaceRoot object owes no TLB work — the flush set is empty, so the wrapper
commits exactly the base operation's result (trace safety for every such retype
call).  `hNew` rules out installing a fresh `.vspaceRoot` (which would rebind —
and hence owe a flush for — its ASID). -/
theorem lifecycleRetypeDirectWithCleanupShootdown_non_vspace
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st : SystemState)
    (hOld : st.getVSpaceRoot? target = none)
    (hNew : retypeInstalledAsid newObj = none) :
    lifecycleRetypeDirectWithCleanupShootdown executingCore authCap target
        newObj st =
      lifecycleRetypeDirectWithCleanup authCap target newObj st := by
  unfold lifecycleRetypeDirectWithCleanupShootdown
  cases h : lifecycleRetypeDirectWithCleanup authCap target newObj st with
  | error e => rfl
  | ok pair =>
      obtain ⟨u, st'⟩ := pair
      cases u
      rw [retypeShootdownAsidList_nil hOld hNew]
      rfl

/-- **WS-SM SM7.B.11**: retyping a live `.vspaceRoot` posts the
`.aside1` shootdown for the destroyed ASID — after the retype commits,
every other core's queue carries the ASID invalidation (or a
superseding full flush), so no core can keep translating through the
dead address space. -/
theorem lifecycleRetypeDirectWithCleanupShootdown_vspace_posts
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    {st stPost : SystemState} {root : VSpaceRoot}
    (hOld : st.getVSpaceRoot? target = some root)
    (h : lifecycleRetypeDirectWithCleanupShootdown executingCore authCap
      target newObj st = .ok ((), stPost)) :
    ∀ c : SeLe4n.Kernel.Concurrency.CoreId, c ≠ executingCore →
      ∃ d ∈ stPost.tlbShootdown.pendingOnCore c,
        d.op = SeLe4n.Kernel.Architecture.encodeAsidInvalidation root.asid ∨
          d.op = SeLe4n.Kernel.Architecture.TlbInvalidation.vmalle1 := by
  unfold lifecycleRetypeDirectWithCleanupShootdown at h
  cases hBase : lifecycleRetypeDirectWithCleanup authCap target newObj st with
  | error e => simp only [hBase] at h; cases h
  | ok pair =>
      obtain ⟨u, stBase⟩ := pair
      cases u
      simp only [hBase, retypeShootdownAsids_eq, Except.ok.injEq, Prod.mk.injEq,
        true_and] at h
      subst h
      intro c hc
      rw [retypeAsidRoundFold_tlbShootdown]
      exact roundFoldSd_covers executingCore
        ((Architecture.mem_shootdownTargets_iff executingCore c).mpr hc)
        (retypeShootdownAsidList st target newObj) root.asid
        (retypeShootdownAsidList_mem_destroyed hOld) stBase.tlbShootdown

/-- WS-SM SM7.B: `lifecycleRetypeDirect` frames the TLB-shootdown state
— the replace bottoms out in `storeObject` (`pendingBounded`
bundle-carriage link). -/
theorem lifecycleRetypeDirect_tlbShootdown_eq
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st st' : SystemState)
    (h : lifecycleRetypeDirect authCap target newObj st = .ok ((), st')) :
    st'.tlbShootdown = st.tlbShootdown := by
  unfold lifecycleRetypeDirect SystemState.getObject? at h
  revert h
  cases hObj : st.objects[target]? with
  | none => intro h; cases h
  | some currentObj =>
      simp only []
      split
      · split
        · intro h
          exact SeLe4n.Model.storeObject_tlbShootdown_eq st target newObj _ h
        · intro h; cases h
      · intro h; cases h

/-- WS-SM SM7.B: the cleanup-composed retype frames the TLB-shootdown
state — the cleanup pipeline
(`lifecyclePreRetypeCleanup_tlbShootdown_eq`), the scrub, and the
replace all leave it untouched. -/
theorem lifecycleRetypeDirectWithCleanup_tlbShootdown_eq
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st st' : SystemState)
    (h : lifecycleRetypeDirectWithCleanup authCap target newObj st
      = .ok ((), st')) :
    st'.tlbShootdown = st.tlbShootdown := by
  unfold lifecycleRetypeDirectWithCleanup SystemState.getObject? at h
  revert h
  split
  · intro h; cases h
  · cases hObj : st.objects[target]? with
    | none =>
        intro h
        exact lifecycleRetypeDirect_tlbShootdown_eq authCap target newObj st st' h
    | some currentObj =>
        simp only []
        cases hClean : lifecyclePreRetypeCleanup st target currentObj newObj with
        | error e => intro h; cases h
        | ok stClean =>
            simp only []
            intro h
            have hRetype := lifecycleRetypeDirect_tlbShootdown_eq authCap target
              newObj (scrubObjectMemory stClean target currentObj.objectType) st' h
            rw [hRetype,
                scrubObjectMemory_tlbShootdown_eq stClean target currentObj.objectType]
            exact lifecyclePreRetypeCleanup_tlbShootdown_eq st stClean target
              currentObj newObj hClean

/-- WS-SM SM7.B: the CSpaceAddr retype wrapper frames the TLB-shootdown
state — cleanup, scrub, and the authority-resolving replace all leave
it untouched. -/
theorem lifecycleRetypeWithCleanup_tlbShootdown_eq
    (authority : CSpaceAddr) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st st' : SystemState)
    (h : lifecycleRetypeWithCleanup authority target newObj st
      = .ok ((), st')) :
    st'.tlbShootdown = st.tlbShootdown := by
  unfold lifecycleRetypeWithCleanup SystemState.getObject? at h
  revert h
  split
  · intro h; cases h
  · cases hObj : st.objects[target]? with
    | none =>
        intro h
        exact lifecycleRetypeObject_tlbShootdown_eq authority target newObj
          st st' h
    | some currentObj =>
        simp only []
        cases hClean : lifecyclePreRetypeCleanup st target currentObj newObj with
        | error e => intro h; cases h
        | ok stClean =>
            simp only []
            intro h
            have hRetype := lifecycleRetypeObject_tlbShootdown_eq authority
              target newObj
              (scrubObjectMemory stClean target currentObj.objectType) st' h
            rw [hRetype,
                scrubObjectMemory_tlbShootdown_eq stClean target
                  currentObj.objectType]
            exact lifecyclePreRetypeCleanup_tlbShootdown_eq st stClean target
              currentObj newObj hClean

/-- **WS-SM SM7.B.11**: **production entry point** — CSpaceAddr-authority
retype with cleanup, scrub, and TLB shootdown; the
`lifecycleRetypeWithCleanup` sibling of
`lifecycleRetypeDirectWithCleanupShootdown`.  The SM7.B storeObject
sweep found this production wrapper still owed the SM7.B.11 TLB work:
retyping a live `.vspaceRoot` through the CSpaceAddr path freed every
page mapping the root held with no TLB maintenance anywhere.  Same
discipline as the Direct form: a live `.vspaceRoot` target's destroyed ASID and
the installed `.vspaceRoot`'s (rebound) ASID are flushed and a `.aside1` round
posted per ASID (`retypeShootdownAsidList`); non-VSpaceRoot retypes into
non-VSpaceRoot objects commit exactly the base operation's state. -/
def lifecycleRetypeWithCleanupShootdown (executingCore :
      SeLe4n.Kernel.Concurrency.CoreId)
    (authority : CSpaceAddr) (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    match lifecycleRetypeWithCleanup authority target newObj st with
    | .error e => .error e
    | .ok ((), st') =>
        retypeShootdownAsids executingCore (retypeShootdownAsidList st target newObj) st'

/-- **WS-SM SM7.B.11 / SM7.F.4(b)(iii)**: a non-VSpaceRoot retype into a
non-VSpaceRoot object through the CSpaceAddr shootdown wrapper commits exactly
the base operation's result (empty flush set). -/
theorem lifecycleRetypeWithCleanupShootdown_non_vspace
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authority : CSpaceAddr) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st : SystemState)
    (hOld : st.getVSpaceRoot? target = none)
    (hNew : retypeInstalledAsid newObj = none) :
    lifecycleRetypeWithCleanupShootdown executingCore authority target
        newObj st =
      lifecycleRetypeWithCleanup authority target newObj st := by
  unfold lifecycleRetypeWithCleanupShootdown
  cases h : lifecycleRetypeWithCleanup authority target newObj st with
  | error e => rfl
  | ok pair =>
      obtain ⟨u, st'⟩ := pair
      cases u
      rw [retypeShootdownAsidList_nil hOld hNew]
      rfl

/-- **WS-SM SM7.B.11**: retyping a live `.vspaceRoot` through the
CSpaceAddr shootdown wrapper posts the `.aside1` round for the
destroyed ASID on every other core (or a superseding full flush). -/
theorem lifecycleRetypeWithCleanupShootdown_vspace_posts
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authority : CSpaceAddr) (target : SeLe4n.ObjId) (newObj : KernelObject)
    {st stPost : SystemState} {root : VSpaceRoot}
    (hOld : st.getVSpaceRoot? target = some root)
    (h : lifecycleRetypeWithCleanupShootdown executingCore authority target
      newObj st = .ok ((), stPost)) :
    ∀ c : SeLe4n.Kernel.Concurrency.CoreId, c ≠ executingCore →
      ∃ d ∈ stPost.tlbShootdown.pendingOnCore c,
        d.op = SeLe4n.Kernel.Architecture.encodeAsidInvalidation root.asid ∨
          d.op = SeLe4n.Kernel.Architecture.TlbInvalidation.vmalle1 := by
  unfold lifecycleRetypeWithCleanupShootdown at h
  cases hBase : lifecycleRetypeWithCleanup authority target newObj st with
  | error e => simp only [hBase] at h; cases h
  | ok pair =>
      obtain ⟨u, stBase⟩ := pair
      cases u
      simp only [hBase, retypeShootdownAsids_eq, Except.ok.injEq, Prod.mk.injEq,
        true_and] at h
      subst h
      intro c hc
      rw [retypeAsidRoundFold_tlbShootdown]
      exact roundFoldSd_covers executingCore
        ((Architecture.mem_shootdownTargets_iff executingCore c).mpr hc)
        (retypeShootdownAsidList st target newObj) root.asid
        (retypeShootdownAsidList_mem_destroyed hOld) stBase.tlbShootdown

/-- WS-SM SM7.B.11: the CSpaceAddr retype-with-shootdown entry point
preserves the shootdown capacity invariant. -/
theorem lifecycleRetypeWithCleanupShootdown_preserves_pendingBounded
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authority : CSpaceAddr) (target : SeLe4n.ObjId) (newObj : KernelObject)
    {st st' : SystemState}
    (hB : Architecture.pendingBounded st.tlbShootdown)
    (hOk : lifecycleRetypeWithCleanupShootdown executingCore authority
      target newObj st = .ok ((), st')) :
    Architecture.pendingBounded st'.tlbShootdown := by
  unfold lifecycleRetypeWithCleanupShootdown at hOk
  cases hBase : lifecycleRetypeWithCleanup authority target newObj st with
  | error e => simp only [hBase] at hOk; cases hOk
  | ok pair =>
      obtain ⟨u, stBase⟩ := pair
      cases u
      have hFrame : stBase.tlbShootdown = st.tlbShootdown :=
        lifecycleRetypeWithCleanup_tlbShootdown_eq authority target newObj
          st stBase hBase
      simp only [hBase, retypeShootdownAsids_eq, Except.ok.injEq, Prod.mk.injEq,
        true_and] at hOk
      subst hOk
      rw [retypeAsidRoundFold_tlbShootdown]
      exact roundFoldSd_preserves_pendingBounded executingCore _ (hFrame ▸ hB)

/-- WS-SM SM7.B.11 / SM7.F.4(b)(iii): the retype-with-shootdown entry point
preserves the shootdown capacity invariant (the 12th `proofLayerInvariantBundle`
conjunct) — the base retype frames the shootdown state; a live `.vspaceRoot`
retype then posts one total coalescing round per flushed ASID (the round-posting
fold preserves the bound). -/
theorem lifecycleRetypeDirectWithCleanupShootdown_preserves_pendingBounded
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    {st st' : SystemState}
    (hB : Architecture.pendingBounded st.tlbShootdown)
    (hOk : lifecycleRetypeDirectWithCleanupShootdown executingCore authCap
      target newObj st = .ok ((), st')) :
    Architecture.pendingBounded st'.tlbShootdown := by
  unfold lifecycleRetypeDirectWithCleanupShootdown at hOk
  cases hBase : lifecycleRetypeDirectWithCleanup authCap target newObj st with
  | error e => simp only [hBase] at hOk; cases hOk
  | ok pair =>
      obtain ⟨u, stBase⟩ := pair
      cases u
      have hFrame : stBase.tlbShootdown = st.tlbShootdown :=
        lifecycleRetypeDirectWithCleanup_tlbShootdown_eq authCap target newObj
          st stBase hBase
      simp only [hBase, retypeShootdownAsids_eq, Except.ok.injEq, Prod.mk.injEq,
        true_and] at hOk
      subst hOk
      rw [retypeAsidRoundFold_tlbShootdown]
      exact roundFoldSd_preserves_pendingBounded executingCore _ (hFrame ▸ hB)

/-- **WS-SM SM7.F.4(b)(iii)** (the shared initiator drain): retire the destroyed
ASID's translations on the **initiator's own** per-core TLB view, atomically with
a live-VSpaceRoot retype's shootdown round.  A retype whose target was a live
`.vspaceRoot` (`getVSpaceRoot? target = some root` on the *pre-state* `stPre`)
makes `root.asid` unresolvable and posts `.aside1` to the **remote** targets
only; this drains the operand on the initiator's own view
(`drainInitiatorPerCoreView` + `encodeAsidInvalidation`, the initiator's local
`TLBI ASIDE1`).  A non-VSpaceRoot retype is a no-op.  Shared by **both**
production retype-with-shootdown wrappers (the Direct-cap and CSpaceAddr forms)
so neither can drift; `perCoreTlb`-only, so trace-safe.

SM7.F.4(b)(iii) extension: the initiator retires **every** ASID in the retype's
flush set (`retypeShootdownAsidList` — the destroyed ASID *and* the installed
`.vspaceRoot`'s rebound ASID), so no core — the initiator included — is left
caching a stale, uncovered translation for a flushed ASID. -/
def retypeInitiatorDrain (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (asids : List SeLe4n.ASID) (st' : SystemState) : SystemState :=
  match asids with
  | [] => st'
  | _ :: _ =>
      Architecture.drainInitiatorPerCoreView st' executingCore
        (asids.map Architecture.encodeAsidInvalidation)

/-- SM8.B.2: the initiator's own per-core TLB drain is scheduler- and
machine-silent, on both arms.

Relocated here at **WS-RR RR8.12 Cut C6g** from the staged non-interference
module, beside the step it frames and beside its sibling
`retypeAsidRoundFold_scheduler`, so a production consumer — the retype
footprint's replenish exactness frame — can read it. -/
@[simp] theorem retypeInitiatorDrain_scheduler
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (asids : List SeLe4n.ASID)
    (st : SystemState) :
    (retypeInitiatorDrain executingCore asids st).scheduler = st.scheduler := by
  unfold retypeInitiatorDrain
  cases asids <;> rfl

@[simp] theorem retypeInitiatorDrain_machine
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (asids : List SeLe4n.ASID)
    (st : SystemState) :
    (retypeInitiatorDrain executingCore asids st).machine = st.machine := by
  unfold retypeInitiatorDrain
  cases asids <;> rfl

/-- **`v0.35.185` (register row 63): and object-silent**, the third member of the
drain's frame family.

It existed as the `.1` of a `private` conjunction in
`IPC/Invariant/DispatchArmPreservation.lean`, whose `.2` duplicated the public
`retypeInitiatorDrain_scheduler` two lines above — so half of it was a second
answer to a question this module already owned, and the half that was new was
unreachable from every module upstream of that one.  Both halves live here now,
beside the step they frame: `v0.35.59`'s rule, which `v0.35.166` paid for the
cleanup's two sweeps and Cut C6g for this same step's scheduler and machine
frames. -/
@[simp] theorem retypeInitiatorDrain_objects
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (asids : List SeLe4n.ASID)
    (st : SystemState) :
    (retypeInitiatorDrain executingCore asids st).objects = st.objects := by
  unfold retypeInitiatorDrain
  cases asids <;> rfl

/-- **WS-SM SM7.F.4(b)(iii)**: for a non-empty flush set the initiator drain is
the per-core view retirement of every operand. -/
theorem retypeInitiatorDrain_of_mem
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    {asids : List SeLe4n.ASID} {a : SeLe4n.ASID} (ha : a ∈ asids)
    (st' : SystemState) :
    retypeInitiatorDrain executingCore asids st' =
      Architecture.drainInitiatorPerCoreView st' executingCore
        (asids.map Architecture.encodeAsidInvalidation) := by
  cases asids with
  | nil => simp at ha
  | cons x xs => rfl

/-- **WS-SM SM7.F.4(b)(iii)** (the shared drain's core property): after the
initiator drain, the initiator's own view holds **no** entry for any flushed
ASID — the "drains the initiator atomically" property both wrappers inherit.
Instantiated at the destroyed ASID by the `_initiator_drained` theorems. -/
theorem retypeInitiatorDrain_drained
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    {asids : List SeLe4n.ASID} {a : SeLe4n.ASID} (ha : a ∈ asids)
    (st' : SystemState) :
    ∀ e ∈ (Architecture.tlbOnCore
        (retypeInitiatorDrain executingCore asids st') executingCore).entries,
      e.asid ≠ a := by
  rw [retypeInitiatorDrain_of_mem executingCore ha]
  intro e he hEq
  rw [Architecture.drainInitiatorPerCoreView_tlbOnCore_self] at he
  have hmem : Architecture.encodeAsidInvalidation a ∈
      asids.map Architecture.encodeAsidInvalidation :=
    List.mem_map.mpr ⟨a, ha, rfl⟩
  have hnm : Architecture.tlbEntryMatches
      (Architecture.encodeAsidInvalidation a) e = false :=
    Architecture.applyTlbInvalidations_survivor_not_matched
      (asids.map Architecture.encodeAsidInvalidation) _ e he
      (Architecture.encodeAsidInvalidation a) hmem
  rw [Architecture.encodeAsidInvalidation_matches a hEq] at hnm
  cases hnm

/-- **WS-SM SM7.F.4(b)(iii)** (the initiator-atomic retype seam — PR #844
review closure): the retype-with-shootdown that additionally retires the
*initiator's own* per-core TLB view for the destroyed ASID **atomically** with
the round posting.  `lifecycleRetypeDirectWithCleanupShootdown` retypes the
object, and — when the retyped object was a live `.vspaceRoot` — flushes the
initiator's scalar TLB and posts a covering `.aside1` descriptor to the
**remote** targets (`shootdownTargets executingCore`, which *excludes* the
initiator).  Once the live `.vspaceMap` fill (SM7.F.4(a)) is operative, the
retyped ASID's translation may be cached on the initiator's own `perCoreTlb`
view; the retype makes that ASID unresolvable, so — without this step — the
initiator's cached entry would be stale **and** uncovered (its queue holds no
descriptor) until the deferred catch-up, making the pending-aware invariant
(`tlbInvalidationConsistent_perCore`) false in the committed intermediate state.
This wrapper closes that gap: it retires the operand on the initiator's own view
(`drainInitiatorPerCoreView` with `encodeAsidInvalidation asid` — the
initiator's local `TLBI ASIDE1`, which real hardware executes synchronously).
The destroyed ASID is read from the **pre-state** (`st.getVSpaceRoot? target`,
before the retype makes it unresolvable), mirroring the base wrapper.
Trace-safe: `perCoreTlb ∉ projectState`, and the drain touches no field the
SGI/round diff-recovery reads. -/
def lifecycleRetypeDirectWithCleanupShootdownPerCore
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    match lifecycleRetypeDirectWithCleanupShootdown executingCore authCap target
        newObj st with
    | .error e => .error e
    | .ok ((), st') =>
        .ok ((), retypeInitiatorDrain executingCore
          (retypeShootdownAsidList st target newObj) st')

/-- **WS-SM SM7.F.4(b)(iii)**: a non-VSpaceRoot retype into a non-VSpaceRoot
object owes no per-core TLB work — the per-core wrapper commits exactly the base
shootdown wrapper's result (empty flush set ⇒ the initiator drain is the
identity; no spurious `perCoreTlb` change). -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCore_non_vspace
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st : SystemState)
    (hOld : st.getVSpaceRoot? target = none)
    (hNew : retypeInstalledAsid newObj = none) :
    lifecycleRetypeDirectWithCleanupShootdownPerCore executingCore authCap target
        newObj st =
      lifecycleRetypeDirectWithCleanupShootdown executingCore authCap target
        newObj st := by
  unfold lifecycleRetypeDirectWithCleanupShootdownPerCore
  cases lifecycleRetypeDirectWithCleanupShootdown executingCore authCap target
      newObj st with
  | error e => rfl
  | ok pair =>
      obtain ⟨u, st'⟩ := pair
      cases u
      rw [retypeShootdownAsidList_nil hOld hNew]
      rfl

/-- **WS-SM SM7.F.4(b)(iii)** (the fix's core property, machine-checked): after
the per-core retype wrapper commits, the **initiator's own** per-core TLB view
holds **no** entry for the destroyed ASID — the drain retired them all (the
initiator's local `TLBI ASIDE1`).  This is exactly the "drains the initiator
atomically" property the finding asked for: once the retype makes `root.asid`
unresolvable, the initiator can no longer be caching a stale, uncovered
translation for it, so the committed post-retype state carries no
stale-and-uncovered entry on the initiator (the reachable pending-aware
invariant violation the plain shootdown wrapper left open). -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCore_initiator_drained
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    {st st' : SystemState} {root : VSpaceRoot}
    (hRoot : st.getVSpaceRoot? target = some root)
    (hStep : lifecycleRetypeDirectWithCleanupShootdownPerCore executingCore
      authCap target newObj st = .ok ((), st')) :
    ∀ e ∈ (Architecture.tlbOnCore st' executingCore).entries, e.asid ≠ root.asid := by
  unfold lifecycleRetypeDirectWithCleanupShootdownPerCore at hStep
  revert hStep
  cases hBase : lifecycleRetypeDirectWithCleanupShootdown executingCore authCap
      target newObj st with
  | error e => intro hStep; cases hStep
  | ok pair =>
      obtain ⟨u, stBase⟩ := pair; cases u
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and]
      intro hStep
      subst hStep
      exact retypeInitiatorDrain_drained executingCore
        (retypeShootdownAsidList_mem_destroyed hRoot) stBase

/-- **WS-SM SM7.F.4(b)(iii)** (the CSpaceAddr sibling — PR #844 review closure):
the initiator-atomic form of the **CSpaceAddr-authority** retype
`lifecycleRetypeWithCleanupShootdown`.  Like the Direct-cap wrapper, it retires
the destroyed ASID on the initiator's own `perCoreTlb` view
(`retypeInitiatorDrain`) atomically with the `.aside1` round the base wrapper
posts to the remote targets — so the CSpaceAddr path is initiator-atomic too,
not just the Direct-cap one.

Said *"production path"* until WS-RR RR8.12's reachability census measured that
no committing `@[export]` reaches this family; the symmetry it keeps with the
Direct-cap form is the point, and the Direct-cap form is the one a syscall
runs.  Trace-safe (`perCoreTlb ∉
projectState`). -/
def lifecycleRetypeWithCleanupShootdownPerCore
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authority : CSpaceAddr) (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    match lifecycleRetypeWithCleanupShootdown executingCore authority target
        newObj st with
    | .error e => .error e
    | .ok ((), st') =>
        .ok ((), retypeInitiatorDrain executingCore
          (retypeShootdownAsidList st target newObj) st')

/-- **WS-SM SM7.F.4(b)(iii)**: a non-VSpaceRoot retype into a non-VSpaceRoot
object through the CSpaceAddr per-core wrapper commits exactly the base shootdown
wrapper's result. -/
theorem lifecycleRetypeWithCleanupShootdownPerCore_non_vspace
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authority : CSpaceAddr) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st : SystemState)
    (hOld : st.getVSpaceRoot? target = none)
    (hNew : retypeInstalledAsid newObj = none) :
    lifecycleRetypeWithCleanupShootdownPerCore executingCore authority target
        newObj st =
      lifecycleRetypeWithCleanupShootdown executingCore authority target
        newObj st := by
  unfold lifecycleRetypeWithCleanupShootdownPerCore
  cases lifecycleRetypeWithCleanupShootdown executingCore authority target
      newObj st with
  | error e => rfl
  | ok pair =>
      obtain ⟨u, st'⟩ := pair
      cases u
      rw [retypeShootdownAsidList_nil hOld hNew]
      rfl

/-- **WS-SM SM7.F.4(b)(iii)** (the CSpaceAddr sibling's core property): after the
CSpaceAddr per-core wrapper commits, the initiator's own view holds **no** entry
for the destroyed ASID — identical guarantee to the Direct-cap form, via the
shared `retypeInitiatorDrain_drained`. -/
theorem lifecycleRetypeWithCleanupShootdownPerCore_initiator_drained
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authority : CSpaceAddr) (target : SeLe4n.ObjId) (newObj : KernelObject)
    {st st' : SystemState} {root : VSpaceRoot}
    (hRoot : st.getVSpaceRoot? target = some root)
    (hStep : lifecycleRetypeWithCleanupShootdownPerCore executingCore
      authority target newObj st = .ok ((), st')) :
    ∀ e ∈ (Architecture.tlbOnCore st' executingCore).entries, e.asid ≠ root.asid := by
  unfold lifecycleRetypeWithCleanupShootdownPerCore at hStep
  revert hStep
  cases hBase : lifecycleRetypeWithCleanupShootdown executingCore authority
      target newObj st with
  | error e => intro hStep; cases hStep
  | ok pair =>
      obtain ⟨u, stBase⟩ := pair; cases u
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and]
      intro hStep
      subst hStep
      exact retypeInitiatorDrain_drained executingCore
        (retypeShootdownAsidList_mem_destroyed hRoot) stBase

-- ============================================================================
-- `v0.36.35`: a VSpace root is never DESTROYED in place.
--
-- `v0.36.9` refused creating a root in place; destroying one fell through the
-- pre-retype cleanup's wildcard, and this section (WS-SM SM7.F.4(b)(iii),
-- `v0.32.90`–`v0.32.93`) proved that the retype-with-shootdown wrappers keep the
-- per-core TLB invariant on exactly that path.  They kept the TLB coherent; they
-- did not finalise the root's page tables, whose pages kept live descriptors and
-- could be reinstalled under a fresh root (the `v0.36.35` security fix,
-- `lifecyclePreRetypeCleanup`'s `.vspaceRoot` arm).  With the path refused, every
-- theorem here stated for a VSpace-root target had an unsatisfiable hypothesis,
-- so they are retired rather than left to read as coverage:
-- `resolveAsidRoot_facts_local`, `lifecyclePreRetypeCleanup_vspaceRoot_id`,
-- `lifecycleRetypeDirectWithCleanup_vspaceRoot_storeObject`,
-- `lifecycleRetypeWithCleanup_vspaceRoot_storeObject`,
-- `retypeStoreObject_tlbEntryConsistent_frame`,
-- `retype_tlbInvariant_of_storeObject`, `retypeShootdownAsidList_mem_installed`
-- (whose one reader they were), and the four
-- `…_preserves_tlbInvalidationConsistent_perCore` theorems of this module (the
-- `…PerCore` and `…PerCoreIcache` forms of both authorities) with the Direct-cap
-- `…_preserves_perCore_memory_invariants` capstone.  What replaces them is the
-- refusal, at each layer the live `.lifecycleRetype` arm is built from.
-- ============================================================================

/-- **`v0.36.35`**: the pre-retype cleanup refuses a VSpace-root target. -/
theorem lifecyclePreRetypeCleanup_vspaceRoot_refused (st : SystemState)
    (target : SeLe4n.ObjId) (root : VSpaceRoot) (newObj : KernelObject) :
    lifecyclePreRetypeCleanup st target (.vspaceRoot root) newObj =
      .error .revocationRequired := by
  unfold lifecyclePreRetypeCleanup
  rfl

/-- **`v0.36.35`** (Direct-cap): a retype of a stored VSpace root never succeeds. -/
theorem lifecycleRetypeDirectWithCleanup_refuses_vspaceRoot
    {st : SystemState} {authCap : Capability} {target : SeLe4n.ObjId}
    {newObj : KernelObject} {root : VSpaceRoot}
    (hVsp : st.objects[target]? = some (.vspaceRoot root)) (r : Unit × SystemState) :
    lifecycleRetypeDirectWithCleanup authCap target newObj st ≠ .ok r := by
  intro hStep
  unfold lifecycleRetypeDirectWithCleanup SystemState.getObject? at hStep
  split at hStep
  · cases hStep
  · simp only [hVsp, lifecyclePreRetypeCleanup_vspaceRoot_refused] at hStep
    cases hStep

/-- **`v0.36.35`** (CSpaceAddr): a retype of a stored VSpace root never succeeds. -/
theorem lifecycleRetypeWithCleanup_refuses_vspaceRoot
    {st : SystemState} {authority : CSpaceAddr} {target : SeLe4n.ObjId}
    {newObj : KernelObject} {root : VSpaceRoot}
    (hVsp : st.objects[target]? = some (.vspaceRoot root)) (r : Unit × SystemState) :
    lifecycleRetypeWithCleanup authority target newObj st ≠ .ok r := by
  intro hStep
  unfold lifecycleRetypeWithCleanup SystemState.getObject? at hStep
  split at hStep
  · cases hStep
  · simp only [hVsp, lifecyclePreRetypeCleanup_vspaceRoot_refused] at hStep
    cases hStep


-- ============================================================================
-- WS-SM SM7.D.1 — Live wiring (b): the `.lifecycleRetype` instruction-cache
-- broadcast.
--
-- A retype re-purposes the target object's backing memory: the transition
-- scrubs it (`scrubObjectMemory`) and installs a different object over it.  Any
-- instruction-cache line a PE holds from that memory therefore describes
-- content that no longer exists — and, because instruction caches are tagged by
-- physical address, such a line stays hittable through *any* later executable
-- mapping of the same frame, in *any* address space.  That is the classic
-- "free, re-allocate, execute the previous owner's code" hazard, and under SMP
-- it must be closed on every core, not just the caller's.
--
-- The *invalidation* is therefore an unconditional domain-wide `IC IALLUIS`,
-- not a targeted `IC IVAU`: the model cannot enumerate which *mappings* alias
-- the retyped object's frame, so the sound choice is the full invalidate.
-- Over-invalidation is always safe — it can only cost re-fetches — whereas
-- under-invalidation is exactly the hazard.  Retype is a rare, already-
-- heavyweight object-lifecycle operation, so the cost lands where it is
-- affordable.
--
-- **The invalidation alone is not enough** (PR #845 review, v0.32.100).  The
-- scrub's zeroing stores land in the *data* cache, and instruction fetches read
-- at the Point of Unification, so until a `DC CVAU` pushes them out the PoU
-- still holds the previous owner's instructions — and `IC IALLUIS`, which
-- issues no clean, merely guarantees that the next fetch goes and re-reads that
-- stale copy.  The operand is therefore `cleanRangeIallu`: clean the scrubbed
-- extent to the PoU, `DSB ISH`, then `IC IALLUIS`.  seL4's `clearMemory` is
-- `memzero` followed by `cleanCacheRange_PoU` for the same reason.
--
-- The extent is nameable, and there is exactly **one** name for it:
-- `scrubExtent` derives `(base, size)` from the pre-state object's `(ObjId,
-- KernelObjectType)`, `scrubObjectMemory` zeroes that range, and
-- `retypeIcacheOp` cleans that same range — both *read* the function rather
-- than recomputing the arithmetic, so the clean cannot come to name a
-- different extent than the zeroing writes
-- (`retypeIcacheOp_cleans_scrub_extent`).
--
-- **Model-level, not hardware-faithful** (PR #845 review round 4).  That
-- extent is the model's abstract allocation convention, *not* the address the
-- untyped allocator would use on hardware: the real child extent is
-- `regionBase + offset` (recorded in state as `UntypedChild.offset` /
-- `.size`).  So on real hardware neither the scrub's stores nor this clean
-- lands on the object's actual backing memory.  That gap is **AN4-G.3 /
-- LIF-M03**, it is the scrub's, not the cache seam's, and it is the reason
-- the clean rides `scrubExtent` instead of a private copy: when the AN9
-- bridge makes the scrub allocator-backed it changes that one function, and
-- this operand follows for free.  Correcting the operand alone would be
-- strictly worse — it would clean an extent the scrub does not zero.
-- ============================================================================

/-- **WS-SM SM7.D**: the instruction-cache maintenance a retype of `target`
owes — clean the extent the retype is about to scrub to the Point of
Unification, then invalidate every instruction cache in the domain.

Read from the **pre**-state, because the operand describes what the transition
is about to destroy: after the fact the old object's type — and with it the
scrub extent — is gone.  When the slot is empty there is nothing to scrub (the
retype installs into a fresh slot), so no clean is owed and the bare domain-wide
invalidate remains, which is conservative rather than clever: the slot's backing
memory may still be cached from an earlier tenant. -/
def retypeIcacheOp (target : SeLe4n.ObjId) (st : SystemState) :
    Architecture.ICacheInvalidation :=
  match st.getObjectType? target with
  | some objType =>
      let extent := scrubExtent target objType
      .cleanRangeIallu extent.fst extent.snd
  | none => .iallu

/-- **WS-SM SM7.D.1**: the retype always owes instruction-cache maintenance. -/
def retypeIcacheOperand (target : SeLe4n.ObjId) (st : SystemState) :
    Option Architecture.ICacheInvalidation :=
  some (retypeIcacheOp target st)

/-- **WS-SM SM7.D.1**: the retype's maintenance is always owed. -/
theorem retypeIcacheOperand_eq (target : SeLe4n.ObjId) (st : SystemState) :
    retypeIcacheOperand target st = some (retypeIcacheOp target st) := rfl

/-- **WS-SM SM7.D**: whichever branch it takes, the retype's operand ends in
`IC IALLUIS` — so every core's instruction cache is cold afterwards, which is
what the seams' 14th-conjunct proofs consume. -/
theorem retypeIcacheOp_isDomainWide (target : SeLe4n.ObjId) (st : SystemState) :
    (retypeIcacheOp target st).isDomainWide = true := by
  unfold retypeIcacheOp
  split <;> rfl

/-- **WS-SM SM7.D** (**the finding's closure**): when the retype will scrub —
i.e. the target slot holds an object — the emitted operand cleans **exactly**
the byte range `scrubObjectMemory` is about to zero.

The right-hand side is stated against `scrubExtent` — **the scrub's own
definition of its range**, not a restatement of this operand's arithmetic.
That is what makes the theorem load-bearing: it relates two *different*
functions, so it fails if either moves independently.  (Before PR #845 review
round 4 the two sides each open-coded the same convention, and the equation
held for any extent whatsoever — it pinned nothing.)

`scrubObjectMemory_cleaned_by_retype` closes the loop by naming the pair the
scrub actually hands to `zeroMemoryRange`. -/
theorem retypeIcacheOp_cleans_scrub_extent {target : SeLe4n.ObjId}
    {st : SystemState} {currentObj : KernelObject}
    (h : st.objects[target]? = some currentObj) :
    retypeIcacheOp target st =
      .cleanRangeIallu
        (scrubExtent target currentObj.objectType).fst
        (scrubExtent target currentObj.objectType).snd := by
  unfold retypeIcacheOp
  rw [SystemState.getObjectType?_eq_some_of_getElem h]

/-- **WS-SM SM7.D** (the correspondence, from the scrub's side): the memory
`scrubObjectMemory` zeroes is exactly the memory the retype's operand cleans
to the Point of Unification.

Stated over `zeroMemoryRange`'s own arguments, so it reads as "every byte the
scrub writes is cleaned" without either side quoting the allocation
convention.  Note this is a statement about the *model's* extent; see the
section header for the AN4-G.3 hardware gap that both sides share. -/
theorem scrubObjectMemory_cleaned_by_retype {target : SeLe4n.ObjId}
    {st : SystemState} {currentObj : KernelObject}
    (h : st.objects[target]? = some currentObj) :
    (scrubObjectMemory st target currentObj.objectType).machine =
      SeLe4n.zeroMemoryRange st.machine
        (scrubExtent target currentObj.objectType).fst
        (scrubExtent target currentObj.objectType).snd ∧
    retypeIcacheOp target st =
      .cleanRangeIallu
        (scrubExtent target currentObj.objectType).fst
        (scrubExtent target currentObj.objectType).snd :=
  ⟨scrubObjectMemory_zeroes_scrubExtent st target currentObj.objectType,
   retypeIcacheOp_cleans_scrub_extent h⟩

/-- **WS-SM SM7.D** (the obligation discharged): the emitted operand discharges
the `.retypeScrub` clean-to-PoU obligation over the scrubbed extent —
`Architecture.dischargesPoUClean` holds for the very `(base, size)` the scrub
writes.

This is what `Architecture.kernelCodeWriteEmitted .retypeScrub = true` asserts,
proven rather than declared.  Note it would be **false** for the pre-v0.32.100
operand `.iallu`, by
`Architecture.ICacheInvalidation.iallu_not_covers_cleanRangeIallu`. -/
theorem retypeIcacheOp_discharges_scrub_obligation {target : SeLe4n.ObjId}
    {st : SystemState} {currentObj : KernelObject}
    (h : st.objects[target]? = some currentObj) :
    Architecture.dischargesPoUClean (retypeIcacheOp target st)
      (scrubExtent target currentObj.objectType).fst
      (scrubExtent target currentObj.objectType).snd = true := by
  rw [retypeIcacheOp_cleans_scrub_extent h]
  simp [Architecture.dischargesPoUClean, Architecture.ICacheInvalidation.covers]

/-- **WS-BP post-landing audit (`v0.36.32`)** (the carve's obligation
discharged): the scrub of a RAM frame records one write, and that write's own
maintenance discharges the `.carveScrub` clean-to-PoU obligation over exactly
the page the scrub zeroes.

The carve's counterpart of `retypeIcacheOp_discharges_scrub_obligation`, with
one difference that is the point: the re-type's operand is recorded **beside**
its scrub, through `withIcacheBroadcast`, while the carve's rides **on** the
scrub's physical write — the HAL performs `PhysicalWrite.icacheMaintenance` as
the last step of `apply_physical_write` — because the zero is itself a deferred
write the seam performs, and a clean recorded as a separate ledger entry could
be emitted in some order other than right after the zero it cleans.  It would
be **false** at the pre-`v0.36.32` model, where the zeroing owed nothing and a
thread could map a freshly carved frame executable with its zeroes still in the
data cache and its previous owner's bytes at the Point of Unification. -/
theorem carveZeroFrame_discharges_carveScrub_obligation (st : SystemState)
    (frame : FrameObject) (hRam : frame.isDevice = false) :
    ∃ w op, (carveZeroFrame st frame).pendingPhysicalWrites =
        st.pendingPhysicalWrites ++ [w] ∧
      w.icacheMaintenance = some op ∧
      Architecture.dischargesPoUClean op frame.base SeLe4n.pageBytes = true := by
  obtain ⟨op, hOp, hDis⟩ := Architecture.zeroPage_discharges_obligation frame.base
  exact ⟨.zeroPage frame.base, op, carveZeroFrame_pendingPhysicalWrites st frame hRam,
    hOp, hDis⟩

/-- **WS-SM SM7.D.1** (**the live `.lifecycleRetype` seam**, Direct-cap
authority): the production retype, complete across both per-core cached
structures.  Layered on SM7.F.4(b)(iii)'s
`lifecycleRetypeDirectWithCleanupShootdownPerCore` (retype + `.aside1`
shootdown round for the destroyed/rebound ASIDs + the initiator's own per-core
TLB drain), it adds the domain-wide `IC IALLUIS` so no core keeps an
instruction line fetched from the re-purposed memory.

Trace-safe: `perCoreICache ∉ projectState`, and the broadcast frames every
field the syscall's round diff-recovery reads. -/
def lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  Architecture.withIcacheBroadcast (retypeIcacheOperand target)
    (lifecycleRetypeDirectWithCleanupShootdownPerCore executingCore authCap
      target newObj)

/-- **WS-SM SM7.D.1**, CSpaceAddr authority: the CSpaceAddr sibling of the live
seam, symmetric with the Direct-cap form so the two cannot drift.

**Not itself a production entry point**, and this docstring said it was until
WS-RR RR8.12's reachability census (`SeLe4n/Testing/KernelTransitionReachability\
Census.lean`) measured that no committing `@[export]` reaches it.  The ABI
resolves a capability at the seam — `syscallResolveCap` runs before dispatch and
`syscallDelegates .lifecycleRetype` names the Direct form — so there is one
authority form a syscall can present and this is not it.  What it is is the
verification surface for the CSpaceAddr path, which is worth having and is a
different claim.

The correction matters beyond this file: *"the live seam"* on a definition
nothing reaches is the same reading that let WS-RR RR8.12's denial-of-service
survive two cuts, where `CancellationBundle`'s header called a composite no
production path calls "the live `.tcbSuspend` dispatch". -/
def lifecycleRetypeWithCleanupShootdownPerCoreIcache
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authority : CSpaceAddr) (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  Architecture.withIcacheBroadcast (retypeIcacheOperand target)
    (lifecycleRetypeWithCleanupShootdownPerCore executingCore authority target
      newObj)

/-- **WS-SM SM7.D.1**: the Direct-cap seam is error-transparent. -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_error_iff
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st : SystemState) (e : KernelError) :
    lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache executingCore authCap
        target newObj st = .error e ↔
      lifecycleRetypeDirectWithCleanupShootdownPerCore executingCore authCap
        target newObj st = .error e :=
  Architecture.withIcacheBroadcast_error_iff _ _ st e

/-- **WS-SM SM7.D.1**: the CSpaceAddr seam is error-transparent. -/
theorem lifecycleRetypeWithCleanupShootdownPerCoreIcache_error_iff
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authority : CSpaceAddr) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st : SystemState) (e : KernelError) :
    lifecycleRetypeWithCleanupShootdownPerCoreIcache executingCore authority
        target newObj st = .error e ↔
      lifecycleRetypeWithCleanupShootdownPerCore executingCore authority target
        newObj st = .error e :=
  Architecture.withIcacheBroadcast_error_iff _ _ st e

/-- **WS-SM SM7.D.1**: on success the Direct-cap seam commits the base
wrapper's state with the domain-wide instruction-cache invalidate applied. -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_ok
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    {st stB : SystemState}
    (hBase : lifecycleRetypeDirectWithCleanupShootdownPerCore executingCore
      authCap target newObj st = .ok ((), stB)) :
    lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache executingCore authCap
        target newObj st =
      .ok ((), Architecture.recordIcacheMaintenance
        (Architecture.icInvalidateBroadcast stB
          Architecture.icBroadcastReach (retypeIcacheOp target st))
        (retypeIcacheOp target st)) :=
  Architecture.withIcacheBroadcast_some_ok (retypeIcacheOperand_eq target st) hBase

/-- **WS-SM SM7.D.1**: on success the CSpaceAddr seam commits the base
wrapper's state with the domain-wide instruction-cache invalidate applied. -/
theorem lifecycleRetypeWithCleanupShootdownPerCoreIcache_ok
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authority : CSpaceAddr) (target : SeLe4n.ObjId) (newObj : KernelObject)
    {st stB : SystemState}
    (hBase : lifecycleRetypeWithCleanupShootdownPerCore executingCore authority
      target newObj st = .ok ((), stB)) :
    lifecycleRetypeWithCleanupShootdownPerCoreIcache executingCore authority
        target newObj st =
      .ok ((), Architecture.recordIcacheMaintenance
        (Architecture.icInvalidateBroadcast stB
          Architecture.icBroadcastReach (retypeIcacheOp target st))
        (retypeIcacheOp target st)) :=
  Architecture.withIcacheBroadcast_some_ok (retypeIcacheOperand_eq target st) hBase

/-- **WS-SM SM7.D.4** (the retype seam's coherency theorem, Direct-cap): after
the production retype every core's instruction cache is **cold**, so the SMP
coherency invariant holds unconditionally — no hypothesis on the pre-state, and
in particular no page-table regularity side conditions.

That is the practical benefit of the unconditional domain-wide invalidate: the
hardest transition in the kernel for cache reasoning (it destroys address
spaces, re-binds ASIDs, and re-purposes memory) becomes the easiest to
discharge, because the post-state has nothing left to be incoherent. -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_preserves_icacheCoherent_perCore
    {executingCore : SeLe4n.Kernel.Concurrency.CoreId}
    {authCap : Capability} {target : SeLe4n.ObjId} {newObj : KernelObject}
    {st st' : SystemState}
    (hStep : lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache executingCore
      authCap target newObj st = .ok ((), st')) :
    Architecture.icacheCoherent_perCore st' := by
  unfold lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache at hStep
  cases hBase : lifecycleRetypeDirectWithCleanupShootdownPerCore executingCore
      authCap target newObj st with
  | error e =>
      rw [(Architecture.withIcacheBroadcast_error_iff _ _ st e).mpr hBase] at hStep
      cases hStep
  | ok pair =>
      obtain ⟨u, stB⟩ := pair; cases u
      rw [Architecture.withIcacheBroadcast_some_ok (retypeIcacheOperand_eq target st) hBase]
        at hStep
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      subst hStep
      intro c l hl
      -- The ledger record frames every core's view; the broadcast emptied them.
      rw [show Architecture.icacheOnCore (Architecture.recordIcacheMaintenance
            (Architecture.icInvalidateBroadcast stB
              Architecture.icBroadcastReach (retypeIcacheOp target st))
            (retypeIcacheOp target st)) c
          = Architecture.icacheOnCore (Architecture.icInvalidateBroadcast stB
              Architecture.icBroadcastReach (retypeIcacheOp target st)) c
          from rfl] at hl
      rw [Architecture.icInvalidateBroadcast_domainWide_empties stB
        Architecture.icBroadcastReach_cover
        (retypeIcacheOp_isDomainWide target st) c] at hl
      cases hl

/-- **WS-SM SM7.D.4** (the retype seam's coherency theorem, CSpaceAddr): the
CSpaceAddr production entry point carries the same unconditional guarantee. -/
theorem lifecycleRetypeWithCleanupShootdownPerCoreIcache_preserves_icacheCoherent_perCore
    {executingCore : SeLe4n.Kernel.Concurrency.CoreId}
    {authority : CSpaceAddr} {target : SeLe4n.ObjId} {newObj : KernelObject}
    {st st' : SystemState}
    (hStep : lifecycleRetypeWithCleanupShootdownPerCoreIcache executingCore
      authority target newObj st = .ok ((), st')) :
    Architecture.icacheCoherent_perCore st' := by
  unfold lifecycleRetypeWithCleanupShootdownPerCoreIcache at hStep
  cases hBase : lifecycleRetypeWithCleanupShootdownPerCore executingCore
      authority target newObj st with
  | error e =>
      rw [(Architecture.withIcacheBroadcast_error_iff _ _ st e).mpr hBase] at hStep
      cases hStep
  | ok pair =>
      obtain ⟨u, stB⟩ := pair; cases u
      rw [Architecture.withIcacheBroadcast_some_ok (retypeIcacheOperand_eq target st) hBase]
        at hStep
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      subst hStep
      intro c l hl
      -- The ledger record frames every core's view; the broadcast emptied them.
      rw [show Architecture.icacheOnCore (Architecture.recordIcacheMaintenance
            (Architecture.icInvalidateBroadcast stB
              Architecture.icBroadcastReach (retypeIcacheOp target st))
            (retypeIcacheOp target st)) c
          = Architecture.icacheOnCore (Architecture.icInvalidateBroadcast stB
              Architecture.icBroadcastReach (retypeIcacheOp target st)) c
          from rfl] at hl
      rw [Architecture.icInvalidateBroadcast_domainWide_empties stB
        Architecture.icBroadcastReach_cover
        (retypeIcacheOp_isDomainWide target st) c] at hl
      cases hl

/-- **`v0.36.35`**: the live `.lifecycleRetype` arm — the Direct-cap
retype with its shootdown, initiator drain and instruction-cache broadcast —
refuses a VSpace-root target: no layer above the base can turn its refusal into
a success, each being error-transparent. -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_refuses_vspaceRoot
    {executingCore : SeLe4n.Kernel.Concurrency.CoreId}
    {st : SystemState} {authCap : Capability} {target : SeLe4n.ObjId}
    {newObj : KernelObject} {root : VSpaceRoot}
    (hVsp : st.objects[target]? = some (.vspaceRoot root)) (r : Unit × SystemState) :
    lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache executingCore authCap target
      newObj st ≠ .ok r := by
  cases hBase : lifecycleRetypeDirectWithCleanup authCap target newObj st with
  | ok r' => exact absurd hBase (lifecycleRetypeDirectWithCleanup_refuses_vspaceRoot hVsp r')
  | error e =>
    have hSh : lifecycleRetypeDirectWithCleanupShootdown executingCore authCap target
        newObj st = .error e := by
      simp only [lifecycleRetypeDirectWithCleanupShootdown, hBase]
    have hPc : lifecycleRetypeDirectWithCleanupShootdownPerCore executingCore authCap
        target newObj st = .error e := by
      simp only [lifecycleRetypeDirectWithCleanupShootdownPerCore, hSh]
    rw [(lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_error_iff executingCore
      authCap target newObj st e).mpr hPc]
    exact fun h => by cases h

/-- **`v0.36.35`**: the CSpaceAddr sibling of the live arm refuses a VSpace-root
target too. -/
theorem lifecycleRetypeWithCleanupShootdownPerCoreIcache_refuses_vspaceRoot
    {executingCore : SeLe4n.Kernel.Concurrency.CoreId}
    {st : SystemState} {authority : CSpaceAddr} {target : SeLe4n.ObjId}
    {newObj : KernelObject} {root : VSpaceRoot}
    (hVsp : st.objects[target]? = some (.vspaceRoot root)) (r : Unit × SystemState) :
    lifecycleRetypeWithCleanupShootdownPerCoreIcache executingCore authority target
      newObj st ≠ .ok r := by
  cases hBase : lifecycleRetypeWithCleanup authority target newObj st with
  | ok r' => exact absurd hBase (lifecycleRetypeWithCleanup_refuses_vspaceRoot hVsp r')
  | error e =>
    have hSh : lifecycleRetypeWithCleanupShootdown executingCore authority target
        newObj st = .error e := by
      simp only [lifecycleRetypeWithCleanupShootdown, hBase]
    have hPc : lifecycleRetypeWithCleanupShootdownPerCore executingCore authority
        target newObj st = .error e := by
      simp only [lifecycleRetypeWithCleanupShootdownPerCore, hSh]
    rw [(lifecycleRetypeWithCleanupShootdownPerCoreIcache_error_iff executingCore
      authority target newObj st e).mpr hPc]
    exact fun h => by cases h

end SeLe4n.Kernel
