/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.ScrubAndUntyped

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
    ¬(tcb.tid ∈ st'.scheduler.runQueue) := by
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
      state := .idle, waitingThreads := [], pendingBadge := none
    })
  | 3 => .ok (.cnode {
      depth := 0, guardWidth := 0, guardValue := 0,
      radixWidth := 0, slots := SeLe4n.Kernel.RobinHood.RHTable.empty 16
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
  | _ + 6 => .error .invalidTypeTag

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
      state := .idle, waitingThreads := [], pendingBadge := none
    }
  | .cnode => .cnode {
      depth := 0, guardWidth := 0, guardValue := 0,
      radixWidth := 0, slots := SeLe4n.Kernel.RobinHood.RHTable.empty 16
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


end SeLe4n.Kernel
