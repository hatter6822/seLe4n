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

end SeLe4n.Kernel
