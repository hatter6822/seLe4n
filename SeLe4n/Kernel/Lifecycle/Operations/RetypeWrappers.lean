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
    -- T5-D: Validate new object well-formedness before proceeding
    if ¬ newObj.wellFormed st.objects then
      .error .illegalState
    else
      match st.objects[target]? with
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
  unfold lifecycleRetypeWithCleanup at hStep
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
      cases hDon : cleanupDonatedSchedContext st tcb.tid with
      | error e => rw [hDon] at hClean; simp at hClean
      | ok stDon =>
        rw [hDon] at hClean; simp only [] at hClean
        -- PR #822 review: the final `.tcb` arm rejects a TCB still holding a reply
        -- link (`.error`, vacuous on `.ok`); reduce the reject-`if` on the `.ok` path.
        have hRO : tcb.replyObject.isSome = false := by
          cases hr : tcb.replyObject.isSome with
          | false => rfl
          | true => rw [if_pos hr] at hClean; exact absurd hClean (by simp)
        rw [if_neg (by simp [hRO])] at hClean
        injection hClean with hClean; subst hClean
        -- S-05/PERF-O1: cleanupTcbReferences_removes_from_runnable is polymorphic in
        -- the input state; use _ to let Lean unify with the scThreadIndex-cleaned state
        exact cleanupTcbReferences_removes_from_runnable _ tcb.tid

-- ============================================================================
-- WS-K-D: Lifecycle syscall dispatch helpers
-- ============================================================================

/-- WS-K-D: Map a raw type tag and size hint to a default `KernelObject`.

Tag encoding follows `KernelObjectType` ordinal order:
- 0 = TCB, 1 = Endpoint, 2 = Notification, 3 = CNode, 4 = VSpaceRoot, 5 = Untyped.

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
  | _ + 8 => .error .invalidTypeTag

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
    match st.objects[target]? with
    | none => .error .objectNotFound
    | some currentObj =>
        if st.lifecycle.objectTypes[target]? = some currentObj.objectType then
          if lifecycleRetypeAuthority authCap target then
            storeObject target newObj st
          else
            .error .illegalAuthority
        else
          .error .illegalState

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
    -- T5-D: Validate new object well-formedness before proceeding
    if ¬ newObj.wellFormed st.objects then
      .error .illegalState
    else
      match st.objects[target]? with
      | none => lifecycleRetypeDirect authCap target newObj st
      | some currentObj =>
          -- AJ1-A (M-14): Propagate cleanup errors instead of silently ignoring
          match lifecyclePreRetypeCleanup st target currentObj newObj with
          | .error e => .error e
          | .ok stClean =>
            let stScrubbed := scrubObjectMemory stClean target currentObj.objectType
            lifecycleRetypeDirect authCap target newObj stScrubbed

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
every other core.  Non-VSpaceRoot retypes owe no TLB work and commit
exactly the base operation's state. -/
def lifecycleRetypeDirectWithCleanupShootdown (executingCore :
      SeLe4n.Kernel.Concurrency.CoreId)
    (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    match lifecycleRetypeDirectWithCleanup authCap target newObj st with
    | .error e => .error e
    | .ok ((), st') =>
        -- the ASID a retype owes the TLB: retyping a live `.vspaceRoot`
        -- destroys an entire address space at once (every mapping the
        -- root held dies with it), so the whole ASID must be
        -- invalidated on every core; retyping any other object type
        -- frees no mapped pages and owes nothing.  Read through the
        -- AN10-B typed accessor (`getVSpaceRoot?`), never the raw
        -- store.
        match (st.getVSpaceRoot? target).map (·.asid) with
        | none => .ok ((), st')
        | some asid =>
            Architecture.tlbFlushByASIDWithShootdown executingCore asid st'

/-- **WS-SM SM7.B.11**: a non-VSpaceRoot retype owes no TLB work — the
wrapper commits exactly the base operation's result (trace safety for
every existing retype call). -/
theorem lifecycleRetypeDirectWithCleanupShootdown_non_vspace
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st : SystemState)
    (hOld : st.getVSpaceRoot? target = none) :
    lifecycleRetypeDirectWithCleanupShootdown executingCore authCap target
        newObj st =
      lifecycleRetypeDirectWithCleanup authCap target newObj st := by
  unfold lifecycleRetypeDirectWithCleanupShootdown
  rw [hOld]
  cases h : lifecycleRetypeDirectWithCleanup authCap target newObj st with
  | error e => rfl
  | ok pair =>
      obtain ⟨u, st'⟩ := pair
      cases u
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
      ({ op := SeLe4n.Kernel.Architecture.encodeAsidInvalidation root.asid,
         initiator := executingCore } :
          SeLe4n.Kernel.Architecture.TlbShootdownDescriptor) ∈
          stPost.tlbShootdown.pendingOnCore c ∨
        ∃ d' ∈ stPost.tlbShootdown.pendingOnCore c,
          d'.op = SeLe4n.Kernel.Architecture.TlbInvalidation.vmalle1 := by
  unfold lifecycleRetypeDirectWithCleanupShootdown at h
  rw [hOld] at h
  cases hBase : lifecycleRetypeDirectWithCleanup authCap target newObj st with
  | error e => rw [hBase] at h; cases h
  | ok pair =>
      obtain ⟨u, stBase⟩ := pair
      cases u
      rw [hBase] at h
      have h' : (Except.ok ((),
          Architecture.tlbShootdownBroadcastCoalescing
            { stBase with tlb := adapterFlushTlbByAsid stBase.tlb root.asid }
            executingCore
            (Architecture.shootdownTargets executingCore)
            (Architecture.encodeAsidInvalidation root.asid)) :
          Except KernelError (Unit × SystemState)) = .ok ((), stPost) := h
      injection h' with h''
      rw [Prod.mk.injEq] at h''
      obtain ⟨_, hstate⟩ := h''
      subst hstate
      intro c hc
      exact Architecture.postShootdownRoundCoalescing_covered _ executingCore
        (Architecture.shootdownTargets_nodup executingCore)
        (Architecture.encodeAsidInvalidation root.asid) c
        ((Architecture.mem_shootdownTargets_iff executingCore c).mpr hc)

/-- WS-SM SM7.B: `lifecycleRetypeDirect` frames the TLB-shootdown state
— the replace bottoms out in `storeObject` (`pendingBounded`
bundle-carriage link). -/
theorem lifecycleRetypeDirect_tlbShootdown_eq
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st st' : SystemState)
    (h : lifecycleRetypeDirect authCap target newObj st = .ok ((), st')) :
    st'.tlbShootdown = st.tlbShootdown := by
  unfold lifecycleRetypeDirect at h
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
  unfold lifecycleRetypeDirectWithCleanup at h
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
  unfold lifecycleRetypeWithCleanup at h
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
discipline as the Direct form: a live `.vspaceRoot` target's ASID is
flushed locally and a `.aside1` round posted; non-VSpaceRoot retypes
commit exactly the base operation's state. -/
def lifecycleRetypeWithCleanupShootdown (executingCore :
      SeLe4n.Kernel.Concurrency.CoreId)
    (authority : CSpaceAddr) (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    match lifecycleRetypeWithCleanup authority target newObj st with
    | .error e => .error e
    | .ok ((), st') =>
        match (st.getVSpaceRoot? target).map (·.asid) with
        | none => .ok ((), st')
        | some asid =>
            Architecture.tlbFlushByASIDWithShootdown executingCore asid st'

/-- **WS-SM SM7.B.11**: a non-VSpaceRoot retype through the CSpaceAddr
shootdown wrapper commits exactly the base operation's result. -/
theorem lifecycleRetypeWithCleanupShootdown_non_vspace
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authority : CSpaceAddr) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st : SystemState)
    (hOld : st.getVSpaceRoot? target = none) :
    lifecycleRetypeWithCleanupShootdown executingCore authority target
        newObj st =
      lifecycleRetypeWithCleanup authority target newObj st := by
  unfold lifecycleRetypeWithCleanupShootdown
  rw [hOld]
  cases h : lifecycleRetypeWithCleanup authority target newObj st with
  | error e => rfl
  | ok pair =>
      obtain ⟨u, st'⟩ := pair
      cases u
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
      ({ op := SeLe4n.Kernel.Architecture.encodeAsidInvalidation root.asid,
         initiator := executingCore } :
          SeLe4n.Kernel.Architecture.TlbShootdownDescriptor) ∈
          stPost.tlbShootdown.pendingOnCore c ∨
        ∃ d' ∈ stPost.tlbShootdown.pendingOnCore c,
          d'.op = SeLe4n.Kernel.Architecture.TlbInvalidation.vmalle1 := by
  unfold lifecycleRetypeWithCleanupShootdown at h
  rw [hOld] at h
  cases hBase : lifecycleRetypeWithCleanup authority target newObj st with
  | error e => rw [hBase] at h; cases h
  | ok pair =>
      obtain ⟨u, stBase⟩ := pair
      cases u
      rw [hBase] at h
      have h' : (Except.ok ((),
          Architecture.tlbShootdownBroadcastCoalescing
            { stBase with tlb := adapterFlushTlbByAsid stBase.tlb root.asid }
            executingCore
            (Architecture.shootdownTargets executingCore)
            (Architecture.encodeAsidInvalidation root.asid)) :
          Except KernelError (Unit × SystemState)) = .ok ((), stPost) := h
      injection h' with h''
      rw [Prod.mk.injEq] at h''
      obtain ⟨_, hstate⟩ := h''
      subst hstate
      intro c hc
      exact Architecture.postShootdownRoundCoalescing_covered _ executingCore
        (Architecture.shootdownTargets_nodup executingCore)
        (Architecture.encodeAsidInvalidation root.asid) c
        ((Architecture.mem_shootdownTargets_iff executingCore c).mpr hc)

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
  revert hOk
  cases hBase : lifecycleRetypeWithCleanup authority target newObj st with
  | error e => intro hOk; cases hOk
  | ok pair =>
      obtain ⟨u, stBase⟩ := pair
      cases u
      have hFrame : stBase.tlbShootdown = st.tlbShootdown :=
        lifecycleRetypeWithCleanup_tlbShootdown_eq authority target newObj
          st stBase hBase
      simp only []
      cases hAsid : (st.getVSpaceRoot? target).map (·.asid) with
      | none =>
          simp only [Except.ok.injEq, Prod.mk.injEq]
          intro hOk
          rw [← hOk.2, hFrame]
          exact hB
      | some asid =>
          simp only []
          intro hOk
          exact Architecture.tlbFlushByASIDWithShootdown_preserves_pendingBounded
            (hFrame ▸ hB) hOk

/-- WS-SM SM7.B.11: the retype-with-shootdown entry point preserves the
shootdown capacity invariant (the 12th `proofLayerInvariantBundle`
conjunct) — the base retype frames the shootdown state; a live
`.vspaceRoot` retype then posts through the total coalescing round. -/
theorem lifecycleRetypeDirectWithCleanupShootdown_preserves_pendingBounded
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    {st st' : SystemState}
    (hB : Architecture.pendingBounded st.tlbShootdown)
    (hOk : lifecycleRetypeDirectWithCleanupShootdown executingCore authCap
      target newObj st = .ok ((), st')) :
    Architecture.pendingBounded st'.tlbShootdown := by
  unfold lifecycleRetypeDirectWithCleanupShootdown at hOk
  revert hOk
  cases hBase : lifecycleRetypeDirectWithCleanup authCap target newObj st with
  | error e => intro hOk; cases hOk
  | ok pair =>
      obtain ⟨u, stBase⟩ := pair
      cases u
      have hFrame : stBase.tlbShootdown = st.tlbShootdown :=
        lifecycleRetypeDirectWithCleanup_tlbShootdown_eq authCap target newObj
          st stBase hBase
      simp only []
      cases hAsid : (st.getVSpaceRoot? target).map (·.asid) with
      | none =>
          simp only [Except.ok.injEq, Prod.mk.injEq]
          intro hOk
          rw [← hOk.2, hFrame]
          exact hB
      | some asid =>
          simp only []
          intro hOk
          exact Architecture.tlbFlushByASIDWithShootdown_preserves_pendingBounded
            (hFrame ▸ hB) hOk

/-- **WS-SM SM7.F.4(b)(iii)** (the shared initiator drain): retire the destroyed
ASID's translations on the **initiator's own** per-core TLB view, atomically with
a live-VSpaceRoot retype's shootdown round.  A retype whose target was a live
`.vspaceRoot` (`getVSpaceRoot? target = some root` on the *pre-state* `stPre`)
makes `root.asid` unresolvable and posts `.aside1` to the **remote** targets
only; this drains the operand on the initiator's own view
(`drainInitiatorPerCoreView` + `encodeAsidInvalidation`, the initiator's local
`TLBI ASIDE1`).  A non-VSpaceRoot retype is a no-op.  Shared by **both**
production retype-with-shootdown wrappers (the Direct-cap and CSpaceAddr forms)
so neither can drift; `perCoreTlb`-only, so trace-safe. -/
def retypeInitiatorDrain (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (target : SeLe4n.ObjId) (stPre st' : SystemState) : SystemState :=
  match (stPre.getVSpaceRoot? target).map (·.asid) with
  | none => st'
  | some asid =>
      Architecture.drainInitiatorPerCoreView st' executingCore
        [Architecture.encodeAsidInvalidation asid]

/-- **WS-SM SM7.F.4(b)(iii)** (the shared drain's core property): after the
initiator drain for a live-VSpaceRoot retype, the initiator's own view holds
**no** entry for the destroyed ASID — the "drains the initiator atomically"
property both wrappers inherit. -/
theorem retypeInitiatorDrain_drained
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (target : SeLe4n.ObjId)
    {stPre st' : SystemState} {root : VSpaceRoot}
    (hRoot : stPre.getVSpaceRoot? target = some root) :
    ∀ e ∈ (Architecture.tlbOnCore
        (retypeInitiatorDrain executingCore target stPre st') executingCore).entries,
      e.asid ≠ root.asid := by
  unfold retypeInitiatorDrain
  rw [hRoot]
  simp only [Option.map_some]
  intro e he hEq
  rw [Architecture.drainInitiatorPerCoreView_tlbOnCore_self] at he
  have hnm : Architecture.tlbEntryMatches
      (Architecture.encodeAsidInvalidation root.asid) e = false :=
    Architecture.applyTlbInvalidations_survivor_not_matched
      [Architecture.encodeAsidInvalidation root.asid] _ e he
      (Architecture.encodeAsidInvalidation root.asid) (by simp)
  rw [Architecture.encodeAsidInvalidation_matches root.asid hEq] at hnm
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
        .ok ((), retypeInitiatorDrain executingCore target st st')

/-- **WS-SM SM7.F.4(b)(iii)**: a non-VSpaceRoot retype owes no per-core TLB
work — the per-core wrapper commits exactly the base shootdown wrapper's result
(trace safety + no spurious `perCoreTlb` change for every non-address-space
retype). -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCore_non_vspace
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st : SystemState)
    (hOld : st.getVSpaceRoot? target = none) :
    lifecycleRetypeDirectWithCleanupShootdownPerCore executingCore authCap target
        newObj st =
      lifecycleRetypeDirectWithCleanupShootdown executingCore authCap target
        newObj st := by
  unfold lifecycleRetypeDirectWithCleanupShootdownPerCore retypeInitiatorDrain
  rw [hOld]
  cases lifecycleRetypeDirectWithCleanupShootdown executingCore authCap target
      newObj st with
  | error e => rfl
  | ok pair =>
      obtain ⟨u, st'⟩ := pair
      cases u
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
      exact retypeInitiatorDrain_drained executingCore target hRoot

/-- **WS-SM SM7.F.4(b)(iii)** (the CSpaceAddr sibling — PR #844 review closure):
the initiator-atomic form of the **CSpaceAddr-authority** production retype
entry point `lifecycleRetypeWithCleanupShootdown` (`API.lean` entry-point table).
Like the Direct-cap wrapper, it retires the destroyed ASID on the initiator's own
`perCoreTlb` view (`retypeInitiatorDrain`) atomically with the `.aside1` round the
base wrapper posts to the remote targets — so the CSpaceAddr production path is
initiator-atomic too, not just the Direct-cap one.  Trace-safe (`perCoreTlb ∉
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
        .ok ((), retypeInitiatorDrain executingCore target st st')

/-- **WS-SM SM7.F.4(b)(iii)**: a non-VSpaceRoot retype through the CSpaceAddr
per-core wrapper commits exactly the base shootdown wrapper's result. -/
theorem lifecycleRetypeWithCleanupShootdownPerCore_non_vspace
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (authority : CSpaceAddr) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st : SystemState)
    (hOld : st.getVSpaceRoot? target = none) :
    lifecycleRetypeWithCleanupShootdownPerCore executingCore authority target
        newObj st =
      lifecycleRetypeWithCleanupShootdown executingCore authority target
        newObj st := by
  unfold lifecycleRetypeWithCleanupShootdownPerCore retypeInitiatorDrain
  rw [hOld]
  cases lifecycleRetypeWithCleanupShootdown executingCore authority target
      newObj st with
  | error e => rfl
  | ok pair =>
      obtain ⟨u, st'⟩ := pair
      cases u
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
      exact retypeInitiatorDrain_drained executingCore target hRoot

-- ============================================================================
-- WS-SM SM7.F.4(b)(iii): whole-invariant retype preservation
-- (`tlbInvalidationConsistent_perCore`) for the VSpaceRoot-target case.
--
-- The invariant-threatening retype: replacing a *live* `.vspaceRoot` at
-- `target` destroys `root.asid`'s entire address space at once, so every core
-- caching a translation for that ASID would hold a stale entry.  The per-core
-- shootdown wrapper closes this: it retires `root.asid` on the initiator's own
-- `perCoreTlb` view (`retypeInitiatorDrain` — the local `TLBI ASIDE1`) *and*
-- posts a covering `.aside1` descriptor to every remote target.  These lemmas
-- prove the committed post-state satisfies the pending-aware per-core TLB
-- invariant, mirroring `PerCoreTlbModel.lean`'s
-- `vspaceUnmapPageWithShootdownPerCore_preserves_tlbInvalidationConsistent_perCore`
-- with `encodeAsidInvalidation root.asid` as the operand and the retype's
-- `resolveAsidRoot`-frame in place of the page-unmap frame.
-- ============================================================================

/-- WS-SM SM7.F.4(b)(iii) (local re-derivation of the private
`resolveAsidRoot_some_facts` in `Architecture/VSpace.lean`): a successful
`resolveAsidRoot` witnesses its ASID-table entry, the object-store root, and
the `root.asid = asid` self-consistency check that `resolveAsidRoot` enforces. -/
private theorem resolveAsidRoot_facts_local
    (st : SystemState) (asid : SeLe4n.ASID) (rootId : SeLe4n.ObjId) (root : VSpaceRoot)
    (h : Architecture.resolveAsidRoot st asid = some (rootId, root)) :
    st.asidTable[asid]? = some rootId ∧
    st.objects[rootId]? = some (.vspaceRoot root) ∧
    root.asid = asid := by
  unfold Architecture.resolveAsidRoot at h
  cases hA : st.asidTable[asid]? with
  | none => simp [hA] at h
  | some oid =>
    simp [hA] at h
    cases hO : st.objects[oid]? with
    | none => simp [hO] at h
    | some obj =>
      cases obj with
      | vspaceRoot root' =>
        simp [hO] at h
        obtain ⟨hEq, hId, hRoot⟩ := h
        subst hId; subst hRoot
        exact ⟨rfl, hO, hEq⟩
      | tcb _ | endpoint _ | notification _ | cnode _ | untyped _
      | schedContext _ | reply _ => simp [hO] at h

/-- WS-SM SM7.F.4(b)(iii): for a `.vspaceRoot` target the pre-retype cleanup
pipeline is the identity — every `lifecyclePreRetypeCleanup` arm keys off a
`.tcb`/`.endpoint`/`.cnode`/`.reply` current object, so a `.vspaceRoot` current
object falls through every match to `.ok st`. -/
theorem lifecyclePreRetypeCleanup_vspaceRoot_id (st : SystemState)
    (target : SeLe4n.ObjId) (root : VSpaceRoot) (newObj : KernelObject) :
    lifecyclePreRetypeCleanup st target (.vspaceRoot root) newObj = .ok st := by
  unfold lifecyclePreRetypeCleanup
  rfl

/-- WS-SM SM7.F.4(b)(iii): the Direct-cap cleanup-composed retype bottoms out in
`storeObject target newObj` on the scrubbed pre-state — cleanup is the identity
for a `.vspaceRoot` current object, the well-formedness/authority/lifecycle
guards passed (`hStep` is `.ok`), and `lifecycleRetypeDirect` commits via
`storeObject`. -/
theorem lifecycleRetypeDirectWithCleanup_vspaceRoot_storeObject
    {st stB : SystemState} {authCap : Capability} {target : SeLe4n.ObjId}
    {newObj : KernelObject} {root : VSpaceRoot}
    (hVsp : st.objects[target]? = some (.vspaceRoot root))
    (hStep : lifecycleRetypeDirectWithCleanup authCap target newObj st = .ok ((), stB)) :
    storeObject target newObj
        (scrubObjectMemory st target (KernelObject.vspaceRoot root).objectType)
      = .ok ((), stB) := by
  unfold lifecycleRetypeDirectWithCleanup at hStep
  split at hStep
  · cases hStep
  · simp only [hVsp] at hStep
    rw [lifecyclePreRetypeCleanup_vspaceRoot_id] at hStep
    unfold lifecycleRetypeDirect at hStep
    simp only [scrubObjectMemory_objects_eq, hVsp] at hStep
    split at hStep
    · split at hStep
      · exact hStep
      · cases hStep
    · cases hStep

/-- WS-SM SM7.F.4(b)(iii): the CSpaceAddr-authority cleanup-composed retype
bottoms out in `storeObject target newObj` on the scrubbed pre-state — same
discipline as the Direct-cap form, via `lifecycleRetypeObject_ok_as_storeObject`. -/
theorem lifecycleRetypeWithCleanup_vspaceRoot_storeObject
    {st stB : SystemState} {authority : CSpaceAddr} {target : SeLe4n.ObjId}
    {newObj : KernelObject} {root : VSpaceRoot}
    (hVsp : st.objects[target]? = some (.vspaceRoot root))
    (hStep : lifecycleRetypeWithCleanup authority target newObj st = .ok ((), stB)) :
    storeObject target newObj
        (scrubObjectMemory st target (KernelObject.vspaceRoot root).objectType)
      = .ok ((), stB) := by
  unfold lifecycleRetypeWithCleanup at hStep
  split at hStep
  · cases hStep
  · simp only [hVsp] at hStep
    rw [lifecyclePreRetypeCleanup_vspaceRoot_id] at hStep
    obtain ⟨_, _, _, _, _, _, hStore⟩ :=
      lifecycleRetypeObject_ok_as_storeObject _ stB authority target newObj hStep
    exact hStore

/-- WS-SM SM7.F.4(b)(iii) (the retype page-table frame): a cached entry whose
ASID is **not** the destroyed `root.asid` stays `tlbEntryConsistent` across the
retype's `storeObject`.  The old `.vspaceRoot root` at `target` is replaced; a
consistent entry `e` resolves `e.asid` to some *other* root `rootId ≠ target`
(the resolution's `root.asid = asid` check forces `rootId ≠ target` since
`e.asid ≠ root.asid`), and that root object is untouched (`storeObject_objects_ne`)
while `e.asid`'s ASID-table binding survives the old-root erase (`e.asid ≠
root.asid`).  `hNoRebind` rules out the one unsound case: retyping into a fresh
`.vspaceRoot` whose ASID collides with another *live* ASID would silently rebind
it (the `asidTable.insert`), leaving `e` stale-and-uncovered — real hardware
retype installs an unbound ASID (0), so the live path always satisfies it. -/
private theorem retypeStoreObject_tlbEntryConsistent_frame
    {st stScr stB : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    {root : VSpaceRoot}
    (hScrObj : stScr.objects = st.objects) (hScrAsid : stScr.asidTable = st.asidTable)
    (hVsp : st.objects[target]? = some (.vspaceRoot root))
    (hObjK : st.objects.invExtK) (hAsidK : st.asidTable.invExtK)
    (hNoRebind : ∀ nr : VSpaceRoot, newObj = KernelObject.vspaceRoot nr →
       nr.asid = root.asid ∨ st.asidTable[nr.asid]? = none)
    (hStore : storeObject target newObj stScr = .ok ((), stB))
    {e : TlbEntry} (hNe : e.asid ≠ root.asid)
    (hCon : Architecture.tlbEntryConsistent st e) :
    Architecture.tlbEntryConsistent stB e := by
  obtain ⟨rootId, r, hres, hlk⟩ := hCon
  obtain ⟨hTbl, hObjRoot, hRasid⟩ := resolveAsidRoot_facts_local st e.asid rootId r hres
  have hRootIdNe : rootId ≠ target := by
    intro hEqId
    apply hNe
    have hobj : some (KernelObject.vspaceRoot root) = some (KernelObject.vspaceRoot r) := by
      rw [← hVsp, ← hObjRoot, hEqId]
    injection hobj with h1
    injection h1 with h2
    rw [h2]; exact hRasid.symm
  have hScrObjInv : stScr.objects.invExt := by rw [hScrObj]; exact hObjK.1
  have hObjTargetScr : stScr.objects[target]? = some (KernelObject.vspaceRoot root) := by
    rw [hScrObj]; exact hVsp
  have hAsidInv : (match stScr.objects[target]? with
      | some (.vspaceRoot oldRoot) => stScr.asidTable.erase oldRoot.asid
      | _ => stScr.asidTable).invExt := by
    rw [hObjTargetScr, hScrAsid]
    exact st.asidTable.erase_preserves_invExt root.asid hAsidK.1 hAsidK.2.1
  have herase : (st.asidTable.erase root.asid)[e.asid]? = st.asidTable[e.asid]? :=
    st.asidTable.getElem?_erase_ne_K root.asid e.asid
      (by intro hb; exact hNe (eq_of_beq hb).symm) hAsidK
  refine ⟨rootId, r,
    Architecture.resolveAsidRoot_of_asidTable_entry stB e.asid rootId r ?_ ?_ hRasid, hlk⟩
  · -- stB.asidTable[e.asid]? = some rootId
    cases newObj with
    | vspaceRoot newRoot =>
        have hNeNew : e.asid ≠ newRoot.asid := by
          intro hEq
          rcases hNoRebind newRoot rfl with hEqA | hNone
          · exact hNe (hEq.trans hEqA)
          · rw [← hEq, hTbl] at hNone; cases hNone
        have hMid := storeObject_asidTable_vspaceRoot_ne stScr stB target newRoot
          e.asid hNeNew hAsidInv hStore
        simp only [hObjTargetScr] at hMid
        rw [hMid, hScrAsid, herase]
        exact hTbl
    | tcb _ | endpoint _ | notification _ | cnode _ | untyped _
    | schedContext _ | reply _ =>
        have hAt := storeObject_asidTable_non_vspaceRoot stScr stB target _
          (by intro nr h; cases h) hStore
        simp only [hObjTargetScr] at hAt
        rw [hAt, hScrAsid, herase]
        exact hTbl
  · -- stB.objects[rootId]? = some (.vspaceRoot r)
    rw [storeObject_objects_ne stScr stB target rootId newObj hRootIdNe hScrObjInv hStore,
      hScrObj]
    exact hObjRoot

/-- WS-SM SM7.F.4(b)(iii) (the per-core reasoning behind the whole-invariant
theorem): from a quiescent, per-core-consistent pre-state, the committed
post-state of the initiator-atomic VSpaceRoot retype — initiator view retired
(`drainInitiatorPerCoreView`) over the round posting
(`tlbShootdownBroadcastCoalescing`) over the retype-`storeObject`-then-scalar-flush
`{ stB with tlb := adapterFlushTlbByAsid … }` — satisfies the pending-aware
per-core invariant.  Per core: the **initiator** has `root.asid` retired on its
own view, so every survivor is non-matching and rides the retype's page-table
frame (`retypeStoreObject_tlbEntryConsistent_frame`, the *consistent* disjunct);
a **remote** core keeps its view but the round posted a covering `.aside1`
descriptor (`postShootdownRoundCoalescing_covered`), so a now-stale matching
entry rides the *pending* disjunct while a non-matching entry rides the
*consistent* one. -/
private theorem retype_tlbInvariant_of_storeObject
    {executingCore : SeLe4n.Kernel.Concurrency.CoreId}
    {target : SeLe4n.ObjId} {newObj : KernelObject}
    {st stScr stB : SystemState} {root : VSpaceRoot}
    (hq : Architecture.shootdownQuiescent st.tlbShootdown)
    (hConsist : Architecture.tlbInvalidationConsistent_perCore st)
    (hVsp : st.objects[target]? = some (.vspaceRoot root))
    (hObjK : st.objects.invExtK) (hAsidK : st.asidTable.invExtK)
    (hNoRebind : ∀ nr : VSpaceRoot, newObj = KernelObject.vspaceRoot nr →
       nr.asid = root.asid ∨ st.asidTable[nr.asid]? = none)
    (hScrObj : stScr.objects = st.objects)
    (hScrAsid : stScr.asidTable = st.asidTable)
    (hScrPct : stScr.perCoreTlb = st.perCoreTlb)
    (hStore : storeObject target newObj stScr = .ok ((), stB)) :
    Architecture.tlbInvalidationConsistent_perCore
      (Architecture.drainInitiatorPerCoreView
        (Architecture.tlbShootdownBroadcastCoalescing
          { stB with tlb := adapterFlushTlbByAsid stB.tlb root.asid }
          executingCore (Architecture.shootdownTargets executingCore)
          (Architecture.encodeAsidInvalidation root.asid))
        executingCore [Architecture.encodeAsidInvalidation root.asid]) := by
  have hpct : stB.perCoreTlb = st.perCoreTlb :=
    (storeObject_perCoreTlb_eq stScr target newObj ((), stB) hStore).trans hScrPct
  have hview : ∀ d, Architecture.tlbOnCore
      (Architecture.tlbShootdownBroadcastCoalescing
        { stB with tlb := adapterFlushTlbByAsid stB.tlb root.asid }
        executingCore (Architecture.shootdownTargets executingCore)
        (Architecture.encodeAsidInvalidation root.asid)) d =
        Architecture.tlbOnCore st d := by
    intro d
    show stB.perCoreTlb.get d = st.perCoreTlb.get d
    rw [hpct]
  have hAllCon : ∀ d, ∀ e ∈ (Architecture.tlbOnCore st d).entries,
      Architecture.tlbEntryConsistent st e :=
    fun d e hmem => Architecture.tlbEntryConsistent_of_ok_of_quiescent hq (hConsist d e hmem)
  have hObjPost : (Architecture.drainInitiatorPerCoreView
      (Architecture.tlbShootdownBroadcastCoalescing
        { stB with tlb := adapterFlushTlbByAsid stB.tlb root.asid }
        executingCore (Architecture.shootdownTargets executingCore)
        (Architecture.encodeAsidInvalidation root.asid))
      executingCore [Architecture.encodeAsidInvalidation root.asid]).objects = stB.objects := rfl
  have hAsidPost : (Architecture.drainInitiatorPerCoreView
      (Architecture.tlbShootdownBroadcastCoalescing
        { stB with tlb := adapterFlushTlbByAsid stB.tlb root.asid }
        executingCore (Architecture.shootdownTargets executingCore)
        (Architecture.encodeAsidInvalidation root.asid))
      executingCore [Architecture.encodeAsidInvalidation root.asid]).asidTable = stB.asidTable := rfl
  intro c e he
  by_cases hc : c = executingCore
  · subst c
    rw [Architecture.drainInitiatorPerCoreView_tlbOnCore_self] at he
    have hmemB := Architecture.mem_of_mem_applyTlbInvalidations he
    rw [hview executingCore] at hmemB
    have hnm : Architecture.tlbEntryMatches
        (Architecture.encodeAsidInvalidation root.asid) e = false :=
      Architecture.applyTlbInvalidations_survivor_not_matched
        [Architecture.encodeAsidInvalidation root.asid] _ e he
        (Architecture.encodeAsidInvalidation root.asid) (by simp)
    have hNe : e.asid ≠ root.asid := by
      intro hEq
      rw [Architecture.encodeAsidInvalidation_matches root.asid hEq] at hnm
      cases hnm
    have hConF : Architecture.tlbEntryConsistent stB e :=
      retypeStoreObject_tlbEntryConsistent_frame hScrObj hScrAsid hVsp hObjK hAsidK
        hNoRebind hStore hNe (hAllCon executingCore e hmemB)
    exact Or.inl (Architecture.tlbEntryConsistent_of_frame hObjPost hAsidPost hConF)
  · rw [Architecture.drainInitiatorPerCoreView_tlbOnCore_ne _
      [Architecture.encodeAsidInvalidation root.asid] (Ne.symm hc)] at he
    rw [hview c] at he
    by_cases hb : Architecture.tlbEntryMatches
        (Architecture.encodeAsidInvalidation root.asid) e = true
    · right
      have hpendEq : (Architecture.drainInitiatorPerCoreView
          (Architecture.tlbShootdownBroadcastCoalescing
            { stB with tlb := adapterFlushTlbByAsid stB.tlb root.asid }
            executingCore (Architecture.shootdownTargets executingCore)
            (Architecture.encodeAsidInvalidation root.asid))
          executingCore [Architecture.encodeAsidInvalidation root.asid]).tlbShootdown.pendingOnCore c =
          (Architecture.postShootdownRoundCoalescing stB.tlbShootdown
            executingCore (Architecture.shootdownTargets executingCore)
            (Architecture.encodeAsidInvalidation root.asid)).pendingOnCore c := rfl
      have hcov := Architecture.postShootdownRoundCoalescing_covered stB.tlbShootdown
        executingCore (Architecture.shootdownTargets_nodup executingCore)
        (Architecture.encodeAsidInvalidation root.asid) c
        ((Architecture.mem_shootdownTargets_iff executingCore c).mpr hc)
      rcases hcov with hdirect | ⟨d', hd'mem, hd'op⟩
      · refine ⟨(⟨Architecture.encodeAsidInvalidation root.asid, executingCore⟩ :
          Architecture.TlbShootdownDescriptor), ?_, hb⟩
        rw [hpendEq]; exact hdirect
      · refine ⟨d', ?_, ?_⟩
        · rw [hpendEq]; exact hd'mem
        · rw [hd'op]; exact Architecture.tlbEntryMatches_vmalle1 e
    · have hNe : e.asid ≠ root.asid := by
        intro hEq
        exact hb (Architecture.encodeAsidInvalidation_matches root.asid hEq)
      have hConF : Architecture.tlbEntryConsistent stB e :=
        retypeStoreObject_tlbEntryConsistent_frame hScrObj hScrAsid hVsp hObjK hAsidK
          hNoRebind hStore hNe (hAllCon c e he)
      exact Or.inl (Architecture.tlbEntryConsistent_of_frame hObjPost hAsidPost hConF)

/-- **WS-SM SM7.F.4(b)(iii)** (the whole-invariant retype theorem — Direct-cap
form): the per-core Direct-cap retype-with-shootdown wrapper **preserves the
pending-aware per-core TLB invariant** (`tlbInvalidationConsistent_perCore`, the
13th `proofLayerInvariantBundle` conjunct) for the invariant-threatening
VSpaceRoot-target case, from a quiescent shootdown state (the precondition the
live seam always satisfies — each round is drained and acknowledged in its
catch-up before the next syscall).  Retyping a live `.vspaceRoot` at `target`
destroys `root.asid`'s entire address space; the wrapper retires `root.asid` on
the **initiator's own** `perCoreTlb` view (`retypeInitiatorDrain`, the local
`TLBI ASIDE1`) and posts a covering `.aside1` descriptor to every **remote**
core, so the committed post-state carries no stale-and-uncovered entry on any
core — mirroring
`PerCoreTlbModel.vspaceUnmapPageWithShootdownPerCore_preserves_tlbInvalidationConsistent_perCore`.

`hNoRebind` is the one precondition beyond the plain wrapper's: it forbids the
retype from installing a fresh `.vspaceRoot` whose ASID collides with a
**different live** ASID (which `storeObject`'s `asidTable.insert` would silently
rebind, leaving that ASID's cached entries stale-and-uncovered — the round only
retires `root.asid`).  Real hardware retype installs an unbound ASID (`0`), and
the freeing case (retype into a non-`.vspaceRoot`) satisfies it vacuously, so
every live retype path meets it; without it the theorem is genuinely false
(`KernelObject.wellFormed` places no ASID-freshness constraint on a new
`.vspaceRoot`). -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCore_preserves_tlbInvalidationConsistent_perCore
    {executingCore : SeLe4n.Kernel.Concurrency.CoreId}
    {authCap : Capability} {target : SeLe4n.ObjId} {newObj : KernelObject}
    {st st' : SystemState} {root : VSpaceRoot}
    (hq : Architecture.shootdownQuiescent st.tlbShootdown)
    (hConsist : Architecture.tlbInvalidationConsistent_perCore st)
    (hVsp : st.objects[target]? = some (.vspaceRoot root))
    (hObjK : st.objects.invExtK) (hAsidK : st.asidTable.invExtK)
    (hNoRebind : ∀ nr : VSpaceRoot, newObj = KernelObject.vspaceRoot nr →
       nr.asid = root.asid ∨ st.asidTable[nr.asid]? = none)
    (hStep : lifecycleRetypeDirectWithCleanupShootdownPerCore executingCore authCap target
      newObj st = .ok ((), st')) :
    Architecture.tlbInvalidationConsistent_perCore st' := by
  have hGV : st.getVSpaceRoot? target = some root := by
    unfold SystemState.getVSpaceRoot?; rw [hVsp]
  unfold lifecycleRetypeDirectWithCleanupShootdownPerCore at hStep
  cases hBase : lifecycleRetypeDirectWithCleanup authCap target newObj st with
  | error e =>
      have hSh : lifecycleRetypeDirectWithCleanupShootdown executingCore authCap target
          newObj st = .error e := by
        unfold lifecycleRetypeDirectWithCleanupShootdown; rw [hBase]
      rw [hSh] at hStep; cases hStep
  | ok pairB =>
      obtain ⟨uB, stB⟩ := pairB; cases uB
      have hShoot : lifecycleRetypeDirectWithCleanupShootdown executingCore authCap target
          newObj st = .ok ((),
            Architecture.tlbShootdownBroadcastCoalescing
              { stB with tlb := adapterFlushTlbByAsid stB.tlb root.asid }
              executingCore (Architecture.shootdownTargets executingCore)
              (Architecture.encodeAsidInvalidation root.asid)) := by
        unfold lifecycleRetypeDirectWithCleanupShootdown
        rw [hBase]
        simp only [hGV, Option.map_some]
        unfold Architecture.tlbFlushByASIDWithShootdown Architecture.tlbFlushByASID
        simp only []
        rw [Architecture.withShootdownRound_total]
      rw [hShoot] at hStep
      simp only [retypeInitiatorDrain, hGV, Option.map_some, Except.ok.injEq,
        Prod.mk.injEq, true_and] at hStep
      subst hStep
      exact retype_tlbInvariant_of_storeObject
        (stScr := scrubObjectMemory st target (KernelObject.vspaceRoot root).objectType)
        hq hConsist hVsp hObjK hAsidK hNoRebind rfl rfl rfl
        (lifecycleRetypeDirectWithCleanup_vspaceRoot_storeObject hVsp hBase)

/-- **WS-SM SM7.F.4(b)(iii)** (the whole-invariant retype theorem — CSpaceAddr
sibling): the per-core CSpaceAddr-authority retype-with-shootdown wrapper
`lifecycleRetypeWithCleanupShootdownPerCore` (`API.lean` entry-point table)
**preserves** `tlbInvalidationConsistent_perCore` for the VSpaceRoot-target case,
under the same quiescence + `hNoRebind` preconditions as the Direct-cap form and
via the same shared reasoning (`retype_tlbInvariant_of_storeObject`) — so the
CSpaceAddr production path is whole-invariant-preserving too, not just the
Direct-cap one. -/
theorem lifecycleRetypeWithCleanupShootdownPerCore_preserves_tlbInvalidationConsistent_perCore
    {executingCore : SeLe4n.Kernel.Concurrency.CoreId}
    {authority : CSpaceAddr} {target : SeLe4n.ObjId} {newObj : KernelObject}
    {st st' : SystemState} {root : VSpaceRoot}
    (hq : Architecture.shootdownQuiescent st.tlbShootdown)
    (hConsist : Architecture.tlbInvalidationConsistent_perCore st)
    (hVsp : st.objects[target]? = some (.vspaceRoot root))
    (hObjK : st.objects.invExtK) (hAsidK : st.asidTable.invExtK)
    (hNoRebind : ∀ nr : VSpaceRoot, newObj = KernelObject.vspaceRoot nr →
       nr.asid = root.asid ∨ st.asidTable[nr.asid]? = none)
    (hStep : lifecycleRetypeWithCleanupShootdownPerCore executingCore authority target
      newObj st = .ok ((), st')) :
    Architecture.tlbInvalidationConsistent_perCore st' := by
  have hGV : st.getVSpaceRoot? target = some root := by
    unfold SystemState.getVSpaceRoot?; rw [hVsp]
  unfold lifecycleRetypeWithCleanupShootdownPerCore at hStep
  cases hBase : lifecycleRetypeWithCleanup authority target newObj st with
  | error e =>
      have hSh : lifecycleRetypeWithCleanupShootdown executingCore authority target
          newObj st = .error e := by
        unfold lifecycleRetypeWithCleanupShootdown; rw [hBase]
      rw [hSh] at hStep; cases hStep
  | ok pairB =>
      obtain ⟨uB, stB⟩ := pairB; cases uB
      have hShoot : lifecycleRetypeWithCleanupShootdown executingCore authority target
          newObj st = .ok ((),
            Architecture.tlbShootdownBroadcastCoalescing
              { stB with tlb := adapterFlushTlbByAsid stB.tlb root.asid }
              executingCore (Architecture.shootdownTargets executingCore)
              (Architecture.encodeAsidInvalidation root.asid)) := by
        unfold lifecycleRetypeWithCleanupShootdown
        rw [hBase]
        simp only [hGV, Option.map_some]
        unfold Architecture.tlbFlushByASIDWithShootdown Architecture.tlbFlushByASID
        simp only []
        rw [Architecture.withShootdownRound_total]
      rw [hShoot] at hStep
      simp only [retypeInitiatorDrain, hGV, Option.map_some, Except.ok.injEq,
        Prod.mk.injEq, true_and] at hStep
      subst hStep
      exact retype_tlbInvariant_of_storeObject
        (stScr := scrubObjectMemory st target (KernelObject.vspaceRoot root).objectType)
        hq hConsist hVsp hObjK hAsidK hNoRebind rfl rfl rfl
        (lifecycleRetypeWithCleanup_vspaceRoot_storeObject hVsp hBase)

end SeLe4n.Kernel
