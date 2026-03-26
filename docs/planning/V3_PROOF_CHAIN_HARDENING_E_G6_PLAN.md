# V3-E & V3-G6: Proof Chain Hardening Implementation Plan

**Workstream**: WS-V Phase V3 — Proof Chain Hardening
**Scope**: V3-E (ipcUnwrapCaps Grant=true Loop Composition) + V3-G (pendingMessage Invariant, culminating in V3-G6 Bundle Integration)
**Source Findings**: M-PRF-2 (V3-E), M-PRF-5 (V3-G)
**Dependencies**: V2 complete (v0.22.1) — new syscalls covered by invariant preservation
**Gate Conditions**: `lake build` succeeds; zero `sorry`; `test_full.sh` green
**Estimated Scope**: ~900 lines Lean (proofs), ~0 lines runtime code

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Current State Analysis](#2-current-state-analysis)
3. [V3-E: ipcUnwrapCaps Grant=true Loop Composition](#3-v3-e-ipcunwrapcaps-granttrue-loop-composition)
4. [V3-G: pendingMessage Invariant for Waiting Threads](#4-v3-g-pendingmessage-invariant-for-waiting-threads)
5. [Cross-Cutting Concerns](#5-cross-cutting-concerns)
6. [Execution Order & Dependency Graph](#6-execution-order--dependency-graph)
7. [Risk Assessment & Mitigations](#7-risk-assessment--mitigations)
8. [Testing & Validation Strategy](#8-testing--validation-strategy)
9. [Documentation Synchronization](#9-documentation-synchronization)

---

## 1. Executive Summary

V3-E and V3-G6 are complementary proof-chain hardening tasks within Phase V3
of the WS-V audit remediation workstream. Together they close two medium-priority
proof gaps (M-PRF-2, M-PRF-5) that currently prevent full machine-checked
verification of the IPC subsystem's capability transfer and message-state
consistency properties.

**V3-E** completes the loop composition proof for `ipcUnwrapCaps` when the
endpoint has Grant right. The per-step theorem
(`ipcTransferSingleCap_preserves_capabilityInvariantBundle`) is already fully
proved; what remains is composing it across the fuel-indexed recursive helper
`ipcUnwrapCapsLoop` via structural induction, threading `hSlotCapacity` and
`hCdtPost` preconditions through each iteration.

**V3-G** (sub-tasks G1–G6) introduces a new invariant predicate
`waitingThreadsPendingMessageNone` — asserting that threads blocked on receive
or notification wait have `pendingMessage = none` — and proves its preservation
through all IPC operations. **V3-G6** is the capstone integration task that
wires this predicate into `ipcInvariantFull` and propagates it through all
bundle-level preservation theorems.

Neither task introduces runtime code changes. Both are pure proof additions
that strengthen the verified invariant surface.

---

## 2. Current State Analysis

### 2.1. Invariant Bundle Architecture

The kernel's proof surface is organized in layered invariant bundles:

```
kernelInvariantBundle (Architecture/Invariant.lean:57-63)
  ├── coreIpcInvariantBundle (Capability/Invariant/Preservation.lean:1355-1356)
  │     ├── schedulerInvariantBundle
  │     ├── capabilityInvariantBundle
  │     │     ├── cspaceSlotUnique
  │     │     ├── cspaceLookupSound
  │     │     ├── cspaceSlotCountBounded
  │     │     ├── cdtCompleteness
  │     │     ├── cdtAcyclicity
  │     │     ├── cspaceDepthConsistent
  │     │     └── objects.invExt
  │     └── ipcInvariantFull (IPC/Invariant/Defs.lean:260-262)
  │           ├── ipcInvariant (notification queue well-formedness)
  │           ├── dualQueueSystemInvariant (endpoint queue structure + TCB links)
  │           ├── allPendingMessagesBounded (msg payload size bounds)
  │           └── badgeWellFormed (badge value word-bounded)
  ├── ipcSchedulerCoherenceComponent
  │     ├── runnableThreadIpcReady
  │     ├── blockedOnSendNotRunnable
  │     ├── blockedOnReceiveNotRunnable
  │     ├── blockedOnCallNotRunnable
  │     ├── blockedOnReplyNotRunnable
  │     └── blockedOnNotificationNotRunnable
  ├── contextMatchesCurrent
  └── currentThreadDequeueCoherent
```

**V3-E** targets `capabilityInvariantBundle` preservation through the
`ipcUnwrapCaps` loop. **V3-G6** targets `ipcInvariantFull` by adding a new
`waitingThreadsPendingMessageNone` conjunct.

### 2.2. ipcUnwrapCaps Loop — Current Proof Coverage

**File**: `SeLe4n/Kernel/IPC/Operations/CapTransfer.lean`

The `ipcUnwrapCapsLoop` (line 36, `private`) is a fuel-indexed recursive helper
that processes capabilities one at a time via `ipcTransferSingleCap`. The
existing proof surface includes loop-level preservation theorems for:

| Property | Loop Theorem (private) | Public Wrapper |
|----------|----------------------|----------------|
| `scheduler` equality | `ipcUnwrapCapsLoop_preserves_scheduler` (line 93) | `ipcUnwrapCaps_preserves_scheduler` (line 126) |
| `services` equality | `ipcUnwrapCapsLoop_preserves_services` (line 139) | `ipcUnwrapCaps_preserves_services` (line 172) |
| `objects[oid]?` for `oid ≠ receiverRoot` | `ipcUnwrapCapsLoop_preserves_objects_ne` (line 185) | `ipcUnwrapCaps_preserves_objects_ne` (line 222) |
| Notification object stability | `ipcUnwrapCapsLoop_preserves_ntfn_objects` (line 237) | `ipcUnwrapCaps_preserves_ntfn_objects` (line 278) |
| Endpoint object stability | `ipcUnwrapCapsLoop_preserves_ep_objects` (line 330) | `ipcUnwrapCaps_preserves_ep_objects` (line 368) |
| TCB object stability | `ipcUnwrapCapsLoop_preserves_tcb_objects` (line 384) | `ipcUnwrapCaps_preserves_tcb_objects` (line 422) |
| CNode type at receiverRoot | `ipcUnwrapCapsLoop_preserves_cnode_at_root` (line 441) | (internal) |
| `objects.invExt` | `ipcUnwrapCapsLoop_preserves_objects_invExt` | `ipcUnwrapCaps_preserves_objects_invExt` |

**Gap**: `capabilityInvariantBundle` preservation for the Grant=true path.
Only `ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant` (line 2010)
exists — the trivial case where `grantRight = false` causes zero state mutation.

All existing loop proofs follow an identical induction template:
1. `induction fuel generalizing idx nextBase accResults st`
2. Base case (`fuel = 0`): `simp [ipcUnwrapCapsLoop]`, state unchanged
3. Step case (`fuel' + 1`): case-split on `caps[idx]?` then `ipcTransferSingleCap` result
4. Error branch: recursive call on unchanged state
5. Ok branch: apply per-step preservation lemma, then recurse

The `capabilityInvariantBundle` proof will follow this same template but must
additionally thread two preconditions (`hSlotCapacity`, `hCdtPost`) whose
intermediate-state forms must be derived at each inductive step.

### 2.3. pendingMessage Field — Current Invariant Coverage

**Field**: `TCB.pendingMessage : Option IpcMessage` (Object/Types.lean:381-384)

Currently covered by `allPendingMessagesBounded` (Defs.lean:211-215), which
asserts that when `pendingMessage = some msg`, `msg.bounded` holds. This is a
**payload-level** constraint.

**Not covered**: The **state-level** constraint that threads in waiting states
(`blockedOnReceive`, `blockedOnNotification`) must have `pendingMessage = none`.
This is structurally correct in the implementation (no code path sets
`pendingMessage` without also transitioning `ipcState` out of waiting) but is
not machine-verified.

**Relevant storage operations** (IPC/Operations/Endpoint.lean:64-109):
- `storeTcbIpcState` — updates only `ipcState`, leaves `pendingMessage` unchanged
- `storeTcbPendingMessage` — updates only `pendingMessage`, leaves `ipcState` unchanged
- `storeTcbIpcStateAndMessage` — atomically updates both fields (used in signal wake path)

---

## 3. V3-E: ipcUnwrapCaps Grant=true Loop Composition

### 3.1. Problem Statement (M-PRF-2)

The per-step theorem `ipcTransferSingleCap_preserves_capabilityInvariantBundle`
(Preservation.lean:1935-1985) is fully proved. It shows that a single capability
transfer preserves the 7-component `capabilityInvariantBundle` given:
- `hInv : capabilityInvariantBundle st` — pre-state invariant
- `hSlotCapacity` — receiver CNode can accommodate the insertion
- `hCdtPost : cdtCompleteness st' ∧ cdtAcyclicity st'` — CDT invariants in post-state

The missing proof is the **loop composition**: showing that iterating this
per-step theorem across all capabilities in `ipcUnwrapCapsLoop` preserves the
bundle from the initial state to the final state.

### 3.2. Design Decision: Exposing `ipcUnwrapCapsLoop`

The loop helper is currently `private` (CapTransfer.lean:36). Three options:

| Option | Approach | Trade-off |
|--------|----------|-----------|
| **A. Remove `private`** | Make `ipcUnwrapCapsLoop` module-internal | Simplest; exposes implementation detail but only within kernel namespace |
| **B. Public wrapper** | Add `ipcUnwrapCapsLoop'` with identical signature | No visibility change but code duplication |
| **C. `@[simp]` unfolding lemma** | Add `ipcUnwrapCapsLoop.unfold` lemma exposing recursion structure | Clean but adds proof maintenance burden |

**Recommended: Option A** — Remove `private`. Rationale:
1. All six existing loop-level preservation theorems are already `private` in
   the same file and follow the same fuel-indexed induction. The new
   `capabilityInvariantBundle` preservation theorem will join them.
2. The function is only reachable from within `SeLe4n.Kernel` namespace.
3. The existing proofs already `simp [ipcUnwrapCapsLoop]` — the definition is
   effectively exposed to the proof engine.
4. A `@[simp]` lemma would need careful `@[local simp]` scoping to avoid
   polluting the global simp set, adding unnecessary complexity.

### 3.3. Sub-Task Breakdown

#### V3-E1: Expose `ipcUnwrapCapsLoop` for External Reasoning

**File**: `SeLe4n/Kernel/IPC/Operations/CapTransfer.lean`
**Scope**: Small (~5 lines changed)
**Action**: Remove `private` keyword from `ipcUnwrapCapsLoop` definition (line 36).

```lean
-- Before:
private def ipcUnwrapCapsLoop ...
-- After:
def ipcUnwrapCapsLoop ...
```

**Verification**: `lake build SeLe4n.Kernel.IPC.Operations.CapTransfer`

**Cascading effects**: All existing private loop theorems (lines 93-450+) reference
`ipcUnwrapCapsLoop` by name. Since they are in the same file and already use
`simp [ipcUnwrapCapsLoop]`, removing `private` is backward-compatible. No
downstream modules import `ipcUnwrapCapsLoop` directly — they use the public
`ipcUnwrapCaps` wrappers.

**Risk**: Negligible. If any naming collision arises (unlikely — the name is
unique within the kernel namespace), a simple rename to `ipcUnwrapCapsLoopImpl`
resolves it.

#### V3-E2: State the Loop Invariant Formally

**File**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`
**Scope**: Small (~15-25 lines)
**Location**: After line 2021 (after the noGrant theorem)

Define a predicate capturing the loop invariant at each step:

```lean
/-- V3-E2: Loop invariant for ipcUnwrapCapsLoop. At each recursive step,
the capability invariant bundle is maintained and the receiver CNode
remains capable of accommodating further insertions. -/
private def ipcUnwrapCapsLoop_invariant
    (receiverRoot : SeLe4n.ObjId)
    (st : SystemState) : Prop :=
  capabilityInvariantBundle st ∧
  (∀ cn, st.objects[receiverRoot]? = some (.cnode cn) →
    cn.slotCountBounded)
```

**Design notes**:
- The `slotCountBounded` component captures the `hSlotCapacity` precondition
  in a form that can be threaded through each iteration.
- The `capabilityInvariantBundle` component subsumes `objects.invExt` (needed
  by per-step preservation of object map structure).
- We do NOT need to track `idx`, `nextBase`, or `accResults` in the invariant —
  these are loop-control variables that don't appear in the postcondition.
- The CDT postcondition (`hCdtPost`) is handled externally: the per-step
  theorem takes `cdtCompleteness st' ∧ cdtAcyclicity st'` as a hypothesis,
  and `capabilityInvariantBundle` already includes `cdtCompleteness` and
  `cdtAcyclicity` as components. After each step, the post-state bundle
  provides the CDT precondition for the next step.

**Verification**: `lake build SeLe4n.Kernel.Capability.Invariant.Preservation`

#### V3-E3: Prove Base Case

**File**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`
**Scope**: Small (~20-30 lines)
**Location**: After V3-E2 definition

Prove that when the loop terminates (either `fuel = 0` or `idx ≥ caps.size`,
i.e., `caps[idx]? = none`), the state is unchanged and the invariant trivially
holds:

```lean
/-- V3-E3: Base case — when fuel is exhausted or all caps are processed,
ipcUnwrapCapsLoop returns the input state unchanged. -/
private theorem ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle_base
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : capabilityInvariantBundle st)
    (hStep : ipcUnwrapCapsLoop caps senderRoot receiverRoot idx nextBase
             accResults 0 st = .ok (summary, st')) :
    capabilityInvariantBundle st' := by
  simp [ipcUnwrapCapsLoop] at hStep
  obtain ⟨_, rfl⟩ := hStep
  exact hInv
```

**Proof strategy**: Identical to the base case of every existing loop theorem
(e.g., `ipcUnwrapCapsLoop_preserves_scheduler` lines 100-103). The `fuel = 0`
and `caps[idx]? = none` branches both return `.ok ({ results := accResults }, st)`,
meaning `st' = st`.

**Verification**: `lake build SeLe4n.Kernel.Capability.Invariant.Preservation`

#### V3-E4: Prove Inductive Step

**File**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`
**Scope**: Medium (~80-120 lines)
**Location**: After V3-E3

This is the core proof work. The inductive step must show: given the loop
invariant holds at step `i`, and `ipcTransferSingleCap` preserves
`capabilityInvariantBundle`, the invariant holds at step `i+1`.

**Proof skeleton**:

```lean
/-- V3-E4: Inductive step — if capabilityInvariantBundle holds before
processing cap at index idx, it holds after processing that cap and
continuing the loop. -/
private theorem ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : capabilityInvariantBundle st)
    (hSlotCap : ∀ cn cap', st.objects[receiverRoot]? = some (.cnode cn) →
      (cn.insert nextBase cap').slotCountBounded)
    (hStep : ipcUnwrapCapsLoop caps senderRoot receiverRoot idx nextBase
             accResults fuel st = .ok (summary, st')) :
    capabilityInvariantBundle st' := by
  induction fuel generalizing idx nextBase accResults st with
  | zero =>
    simp [ipcUnwrapCapsLoop] at hStep
    obtain ⟨_, rfl⟩ := hStep; exact hInv
  | succ n ih =>
    simp only [ipcUnwrapCapsLoop] at hStep
    cases hCap : caps[idx]? with
    | none => simp [hCap] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInv
    | some cap =>
      simp [hCap] at hStep
      cases hTransfer : ipcTransferSingleCap cap
          { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
          receiverRoot nextBase maxExtraCaps st with
      | error e =>
        -- Error: state unchanged, recurse with same invariant
        simp [hTransfer] at hStep
        exact ih _ _ _ _ hInv hSlotCap hStep
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        -- Success: apply per-step preservation theorem
        -- 1. Derive capabilityInvariantBundle stNext from per-step theorem
        -- 2. Derive hSlotCap for stNext (slot capacity is monotone under insert)
        -- 3. Apply inductive hypothesis
        sorry -- V3-E4 proof body
```

**Key proof obligations at each step**:

1. **Derive `capabilityInvariantBundle stNext`**: Apply
   `ipcTransferSingleCap_preserves_capabilityInvariantBundle` with:
   - `hInv` (from inductive hypothesis)
   - `hSlotCapacity` (from loop invariant, specialized to current `nextBase`)
   - `hCdtPost` (extracted from `capabilityInvariantBundle stNext` — note this
     is circular; see resolution below)

2. **CDT circularity resolution**: The per-step theorem requires
   `cdtCompleteness st' ∧ cdtAcyclicity st'` as a *hypothesis*. This is an
   externalized postcondition pattern. The proof must establish CDT invariants
   for the intermediate state `stNext` independently of the bundle. Two approaches:
   - **Approach A (preferred)**: Prove separate lemmas
     `ipcTransferSingleCap_preserves_cdtCompleteness` and
     `ipcTransferSingleCap_preserves_cdtAcyclicity` that derive CDT invariants
     from the pre-state CDT invariants. These already exist implicitly within
     `cspaceInsertSlot_preserves_capabilityInvariantBundle` (which the per-step
     theorem delegates to).
   - **Approach B**: Factor `hCdtPost` out of the per-step theorem entirely by
     proving CDT preservation as a separate chain. This requires refactoring the
     existing theorem signature.

   **Recommended**: Approach A — add two focused CDT preservation lemmas for
   `ipcTransferSingleCap`. These are thin wrappers around the existing CSpace
   insert + CDT edge-addition proofs.

3. **Derive `hSlotCap` for next iteration**: After a successful insertion at
   `nextBase`, the CNode at `receiverRoot` has been modified (one more slot
   filled). The slot capacity predicate must hold for the *new* CNode at the
   *new* `nextBase'`. This follows from `slotCountBounded` being a global
   property of the CNode (total slot count ≤ capacity), which is preserved by
   `cspaceInsertSlot_preserves_cspaceSlotCountBounded`.

4. **Case split on `result`**: The three `CapTransferResult` variants
   (`.installed`, `.noSlot`, `.grantDenied`) determine whether `nextBase`
   advances. The proof must handle each variant, mirroring the existing
   pattern in `ipcUnwrapCapsLoop_preserves_scheduler` (lines 121-124).

**Estimated complexity**: This is the hardest sub-task. The proof body will be
~80-120 lines, following the established induction template but with additional
hypothesis threading. The CDT auxiliary lemmas add ~30-40 lines.

**Verification**: `lake build SeLe4n.Kernel.Capability.Invariant.Preservation`

#### V3-E5: Compose Full `ipcUnwrapCaps` Theorem

**File**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`
**Scope**: Medium (~30-50 lines)
**Location**: After V3-E4

Lift the loop-level theorem to the public `ipcUnwrapCaps` entry point:

```lean
/-- V3-E5: ipcUnwrapCaps preserves capabilityInvariantBundle for all values
of grantRight. When grantRight = false, state is unchanged (trivial).
When grantRight = true, applies the loop induction from V3-E4. -/
theorem ipcUnwrapCaps_preserves_capabilityInvariantBundle
    (st st' : SystemState) (msg : IpcMessage)
    (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (summary : CapTransferSummary)
    (hInv : capabilityInvariantBundle st)
    (hSlotCap : ∀ cn cap', st.objects[receiverRoot]? = some (.cnode cn) →
      (cn.insert slotBase cap').slotCountBounded)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    capabilityInvariantBundle st' := by
  unfold ipcUnwrapCaps at hStep
  split at hStep
  · -- grantRight = false: state unchanged
    simp at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInv
  · -- grantRight = true: apply loop theorem
    exact ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle
      _ _ _ _ _ _ _ _ _ _ hInv hSlotCap hStep
```

**This theorem**:
- Subsumes the existing `ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant`
- Is the final deliverable for V3-E
- Plugs directly into the call sites in `endpointSendDual`, `endpointCall`,
  and `endpointReplyRecv` where cap transfer occurs during IPC rendezvous

**Verification**: `lake build SeLe4n.Kernel.Capability.Invariant.Preservation`

### 3.4. V3-E Auxiliary Lemmas Required

Before V3-E4 can proceed, the following helper lemmas must be established:

| Lemma | Purpose | File | Scope |
|-------|---------|------|-------|
| `ipcTransferSingleCap_preserves_cdtCompleteness` | CDT completeness after single cap transfer | `Capability/Invariant/Preservation.lean` | S |
| `ipcTransferSingleCap_preserves_cdtAcyclicity` | CDT acyclicity after single cap transfer | `Capability/Invariant/Preservation.lean` | S |
| `ipcTransferSingleCap_slotCountBounded_next` | Slot capacity monotonicity through single transfer | `Capability/Invariant/Preservation.lean` | S |

These lemmas extract facts that are currently embedded within the existing
per-step bundle proof. They may be provable by decomposing the
`capabilityInvariantBundle stNext` result from the per-step theorem, or by
independent derivation from the component operations (`cspaceInsertSlot`,
`ensureCdtNodeForSlot`, `addEdge`).

### 3.5. V3-E Complete File Change Summary

| File | Lines Added | Lines Modified | Type |
|------|-------------|----------------|------|
| `IPC/Operations/CapTransfer.lean` | 0 | 1 (remove `private`) | Visibility |
| `Capability/Invariant/Preservation.lean` | ~180-220 | 0 | Proof |
| **Total** | **~180-220** | **1** | |

---

## 4. V3-G: pendingMessage Invariant for Waiting Threads

### 4.1. Problem Statement (M-PRF-5)

The `pendingMessage` field in TCB objects is modified by `storeTcbPendingMessage`
and `storeTcbIpcStateAndMessage`. No formal invariant currently constrains the
relationship between a thread's `ipcState` and its `pendingMessage` field.

The implementation is structurally correct: every code path that sets
`pendingMessage := some msg` simultaneously transitions `ipcState` out of
waiting states (to `.ready` or `.blockedOnSend`). But this coupling is not
machine-verified.

**Security relevance**: Without this invariant, a hypothetical bug could leave
a thread in `blockedOnReceive` or `blockedOnNotification` with a stale
`pendingMessage`, causing message duplication or data leakage on the next
dequeue.

### 4.2. Invariant Scope Decision

The audit finding M-PRF-5 specifies the invariant scope as:

> threads with `ipcState ∈ {blockedOnReceive, blockedOnNotification}` must
> have `pendingMessage = none`

**Design question**: Should `blockedOnSend` threads also be constrained?

**Analysis**:
- `blockedOnSend` threads **carry** a pending message (the outgoing payload
  staged for delivery when a receiver arrives). Their `pendingMessage` is
  intentionally `some msg`.
- `blockedOnReceive` threads are waiting to *receive* — they have no outgoing
  payload. `pendingMessage` should be `none`.
- `blockedOnNotification` threads are waiting for a signal — they have no
  outgoing payload. `pendingMessage` should be `none`.
- `blockedOnCall` threads have already sent their message and are waiting for
  a reply. Their `pendingMessage` may be `none` (message already delivered)
  or `some msg` (implementation-dependent staging). **Exclude from scope** —
  the Call semantics are complex and the audit finding specifically scopes to
  receive/notification.
- `blockedOnReply` threads: Similar to Call — exclude from scope.

**Decision**: Scope to `{blockedOnReceive, blockedOnNotification}` as specified
in M-PRF-5. This is the minimal correct scope that addresses the finding
without over-constraining Call/Reply semantics.

### 4.3. Sub-Task Breakdown

#### V3-G1: Define `waitingThreadsPendingMessageNone`

**File**: `SeLe4n/Kernel/IPC/Invariant/Defs.lean`
**Scope**: Small (~15-20 lines)
**Location**: After `badgeWellFormed` definition (line 248), before `ipcInvariantFull` (line 260)

```lean
-- ============================================================================
-- V3-G1/M-PRF-5: Waiting-thread pending-message consistency
-- ============================================================================

/-- V3-G1/M-PRF-5: Threads blocked on receive or notification wait must not
have a staged pending message. This ensures no stale message data can leak
across IPC state transitions.

Scope: `blockedOnReceive` and `blockedOnNotification` states only.
`blockedOnSend` threads intentionally carry `pendingMessage = some msg`
(the outgoing payload). Call/Reply threads are excluded per M-PRF-5 scope. -/
def waitingThreadsPendingMessageNone (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[tid.toObjId]? = some (.tcb tcb) →
    (match tcb.ipcState with
     | .blockedOnReceive _ => true
     | .blockedOnNotification _ => true
     | _ => false) = true →
    tcb.pendingMessage = none
```

**Design notes**:
- Uses match-based predicate rather than two separate implications to keep the
  definition compact and the proof obligations at each call site to a single
  case analysis.
- Alternative formulation using disjunction (`tcb.ipcState = .blockedOnReceive _
  ∨ tcb.ipcState = .blockedOnNotification _`) is equivalent but harder to
  `simp` in proofs due to existential quantification over the endpoint/notification ID.
- The match-based form allows `simp [waitingThreadsPendingMessageNone]` to
  reduce cleanly when the thread's `ipcState` is known.

**Verification**: `lake build SeLe4n.Kernel.IPC.Invariant.Defs`

#### V3-G2: Prove Preservation for `notificationWait`

**File**: `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation.lean`
**Scope**: Small (~30-40 lines)

`notificationWait` transitions a thread from `.ready` to
`.blockedOnNotification oid` and adds it to the notification's waiting list.

**Proof strategy**:
1. For the transitioning thread: Before the operation, it was `.ready` (outside
   invariant scope). After, it is `.blockedOnNotification oid`. We must show
   `pendingMessage = none` for this thread in the post-state.
   - `notificationWait` calls `storeTcbIpcState` which updates `ipcState` only,
     leaving `pendingMessage` unchanged.
   - **Precondition needed**: The thread must have `pendingMessage = none`
     before entering the wait. This follows from a broader property: runnable
     threads with `ipcState = .ready` should have `pendingMessage = none`.
     This is the natural pre-state condition — the thread is entering a wait,
     so it should have no pending message.
   - If this precondition is not directly available, we need a **caller-side
     precondition** that the thread's `pendingMessage = none` before calling
     `notificationWait`.

2. For all other threads: `storeTcbIpcState` only modifies the target thread's
   TCB. Other threads' `ipcState` and `pendingMessage` are unchanged. The
   invariant for non-target threads follows from `storeObject_objects_ne`.

**Key lemma needed**:
```lean
theorem storeTcbIpcState_preserves_waitingThreadsPendingMessageNone
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (newState : ThreadIpcState)
    (hInv : waitingThreadsPendingMessageNone st)
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbIpcState st tid newState = .ok ((), st'))
    -- When transitioning INTO a waiting state, the thread's pendingMessage must be none
    (hPre : ∀ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) →
      (match newState with
       | .blockedOnReceive _ => true
       | .blockedOnNotification _ => true
       | _ => false) = true →
      tcb.pendingMessage = none) :
    waitingThreadsPendingMessageNone st'
```

**Verification**: `lake build SeLe4n.Kernel.IPC.Invariant.NotificationPreservation`

#### V3-G3: Prove Preservation for `notificationSignal` (Wake Path)

**File**: `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation.lean`
**Scope**: Small (~35-50 lines)

The `notificationSignal` wake path (NotificationPreservation.lean:53-75):
1. `storeObject` — updates notification (removes waiter from queue)
2. `storeTcbIpcStateAndMessage` — sets `ipcState := .ready` AND
   `pendingMessage := some { badge := some badge }` (delivers badge)
3. `ensureRunnable` — adds thread to scheduler run queue

**Proof strategy**: The woken thread transitions FROM `.blockedOnNotification`
TO `.ready` while simultaneously receiving a message. Since `.ready` is outside
the invariant's scope, the thread exits the constrained set — no violation.

For all other threads:
- `storeObject` (notification store) does not modify any TCB
- `storeTcbIpcStateAndMessage` only modifies the target thread's TCB
- `ensureRunnable` does not modify any TCB objects (only scheduler state)

The key insight is that `storeTcbIpcStateAndMessage` atomically moves the
thread OUT of the invariant scope (to `.ready`) while setting `pendingMessage`,
so the invariant is trivially preserved for the target thread.

**Proof structure**:
```lean
-- For target thread (waiter):
--   Pre: ipcState = .blockedOnNotification oid (in scope, pendingMessage = none by hInv)
--   Post: ipcState = .ready (OUT of scope — invariant vacuously holds)
-- For non-target threads:
--   TCB unchanged by storeTcbIpcStateAndMessage (storeObject_objects_ne)
--   ipcState and pendingMessage preserved
```

**Verification**: `lake build SeLe4n.Kernel.IPC.Invariant.NotificationPreservation`

#### V3-G4: Prove Preservation for `endpointSend`/`endpointReceive`

**File**: `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean`
**Scope**: Medium (~80-120 lines)

**Endpoint send** (`endpointSendDual`): Two paths —
- **Rendezvous** (receiver waiting): Dequeues receiver from receive queue,
  delivers message, transitions receiver from `.blockedOnReceive` to `.ready`.
  Sender remains `.ready` (or becomes `.blockedOnCall` for Call variant).
  - Receiver exits invariant scope (`.ready`) — trivially preserved.
  - All other threads: TCBs not modified for non-participants.

- **Block** (no receiver): Sender transitions to `.blockedOnSend` with
  `pendingMessage := some msg`. `.blockedOnSend` is outside scope — preserved.

**Endpoint receive** (`endpointReceiveDual`): Two paths —
- **Rendezvous** (sender waiting): Dequeues sender from send queue,
  receives message. Sender transitions from `.blockedOnSend` to `.ready`.
  Receiver was `.ready`, stays `.ready` (or enters `.blockedOnReply`).
  - Sender exits `.blockedOnSend` (out of scope) to `.ready` (out of scope).
  - Invariant: only `.blockedOnReceive`/`.blockedOnNotification` threads matter,
    and none of them are touched by this operation.

- **Block** (no sender): Receiver transitions from `.ready` to
  `.blockedOnReceive oid`. `pendingMessage` is NOT set (receiver has no
  outgoing message). Must show `pendingMessage = none` — follows from the
  receiver's `.ready` state having no pending message (precondition from
  the calling context or the broader scheduler-IPC coherence).

**Key helper lemma** (reusable across G4 and G5):
```lean
/-- Dual-queue popHead + storeTcbIpcStateAndMessage preserves the invariant
when the dequeued thread transitions to .ready (exiting scope). -/
private theorem dualQueuePopHead_wake_preserves_waitingThreadsPendingMessageNone ...
```

**Sub-steps for V3-G4**:
1. Prove `endpointQueueEnqueue_preserves_waitingThreadsPendingMessageNone`
   (frame lemma — queue ops don't modify TCB ipcState/pendingMessage)
2. Prove `endpointQueuePopHead_preserves_waitingThreadsPendingMessageNone`
   (frame lemma — queue ops modify endpoint object, not TCBs)
3. Prove `endpointSendDual_preserves_waitingThreadsPendingMessageNone`
   (composes queue + TCB store preservation)
4. Prove `endpointReceiveDual_preserves_waitingThreadsPendingMessageNone`
   (composes queue + TCB store preservation)

**Verification**: `lake build SeLe4n.Kernel.IPC.Invariant.EndpointPreservation`

#### V3-G5: Prove Preservation for `endpointCall`/`endpointReplyRecv`

**File**: `SeLe4n/Kernel/IPC/Invariant/CallReplyRecv.lean`
**Scope**: Medium (~80-120 lines)

**`endpointCall`**: Compound operation = send + block-on-reply.
- Send leg: follows `endpointSendDual` preservation (V3-G4)
- Block-on-reply leg: caller transitions to `.blockedOnReply oid`. This is
  outside the invariant scope — preserved.

**`endpointReplyRecv`**: Compound operation = reply + receive.
- Reply leg: wakes the reply-blocked thread (`.blockedOnReply` → `.ready`).
  Outside scope — preserved.
- Receive leg: follows `endpointReceiveDual` preservation (V3-G4)

**`endpointReply`**: Wakes a reply-blocked thread. Outside scope — preserved.

**Sub-steps**:
1. Prove `endpointCall_preserves_waitingThreadsPendingMessageNone`
2. Prove `endpointReply_preserves_waitingThreadsPendingMessageNone`
3. Prove `endpointReplyRecv_preserves_waitingThreadsPendingMessageNone`

Each proof composes the primitive preservation lemmas from V3-G4 with
the Call/Reply operation structure.

**Verification**: `lake build SeLe4n.Kernel.IPC.Invariant.CallReplyRecv`

#### V3-G6: Integrate into `ipcInvariantFull` and Bundle Theorems

**Files**: `IPC/Invariant/Defs.lean`, `IPC/Invariant/Structural.lean`,
`Capability/Invariant/Preservation.lean`
**Scope**: Small (~40-60 lines across 3 files)

**Step 1**: Add `waitingThreadsPendingMessageNone` to `ipcInvariantFull`
(Defs.lean:260-262):

```lean
-- Before:
def ipcInvariantFull (st : SystemState) : Prop :=
  ipcInvariant st ∧ dualQueueSystemInvariant st ∧ allPendingMessagesBounded st ∧
  badgeWellFormed st

-- After:
def ipcInvariantFull (st : SystemState) : Prop :=
  ipcInvariant st ∧ dualQueueSystemInvariant st ∧ allPendingMessagesBounded st ∧
  badgeWellFormed st ∧ waitingThreadsPendingMessageNone st
```

**Step 2**: Update extractor theorems in `Preservation.lean`:

```lean
-- Add new extractor:
theorem coreIpcInvariantBundle_to_waitingThreadsPendingMessageNone
    {st : SystemState} (h : coreIpcInvariantBundle st) :
    waitingThreadsPendingMessageNone st :=
  h.2.2.2.2.2.2  -- path through the conjunction chain
```

**Note**: Adding a conjunct to `ipcInvariantFull` changes the destructuring
paths for ALL existing extractors. The existing extractors are:
- `coreIpcInvariantBundle_to_ipcInvariant` → `h.2.2.1` (unchanged)
- `coreIpcInvariantBundle_to_dualQueueSystemInvariant` → `h.2.2.2.1` (unchanged)
- `coreIpcInvariantBundle_to_allPendingMessagesBounded` → `h.2.2.2.2.1` (unchanged)
- `coreIpcInvariantBundle_to_badgeWellFormed` → `h.2.2.2.2.2` → becomes `h.2.2.2.2.2.1`

**This is a breaking change** to `coreIpcInvariantBundle_to_badgeWellFormed`.
The fix is a single-character edit (`.2` → `.2.1`) but must be identified and
applied. All call sites of this extractor must be audited.

**Step 3**: Update all bundle-level preservation theorems in `Structural.lean`
that reconstruct `ipcInvariantFull` to include the new component. These
theorems take individual component preservation proofs and compose them into
the bundle. Each must be extended to thread the new
`waitingThreadsPendingMessageNone` preservation proof.

**Step 4**: Update `lifecycleRetypeObject_preserves_coreIpcInvariantBundle`
(Preservation.lean:1534) to include the new component. Lifecycle retype creates
new objects — the new invariant is trivially preserved because retype does not
modify existing TCB `ipcState` or `pendingMessage` fields.

**Cascading bundle updates** (files that reconstruct `ipcInvariantFull` or
`coreIpcInvariantBundle`):

| File | Theorem | Change |
|------|---------|--------|
| `Capability/Invariant/Preservation.lean` | `coreIpcInvariantBundle_to_badgeWellFormed` | Fix path `.2.2.2.2.2` → `.2.2.2.2.2.1` |
| `Capability/Invariant/Preservation.lean` | `lifecycleRetypeObject_preserves_coreIpcInvariantBundle` | Add component |
| `IPC/Invariant/Structural.lean` | Bundle reconstruction theorems | Add component |
| `Architecture/Invariant.lean` | `kernelInvariantBundle` composition | May need update if it decomposes `ipcInvariantFull` |

**Verification**: `lake build SeLe4n.Kernel.IPC.Invariant.Structural` then
`lake build SeLe4n.Kernel.Architecture.Invariant`

### 4.4. V3-G Shared Infrastructure Lemmas

The following frame/transport lemmas are needed across multiple V3-G sub-tasks:

| Lemma | Purpose | Reused By |
|-------|---------|-----------|
| `storeObject_preserves_waitingThreadsPendingMessageNone_non_tcb` | Storing non-TCB objects (endpoints, notifications) preserves the invariant | G2, G3, G4, G5 |
| `storeObject_tcb_preserves_waitingThreadsPendingMessageNone` | Storing a TCB preserves the invariant when the new TCB satisfies the predicate or exits scope | G2, G3, G4, G5 |
| `ensureRunnable_preserves_waitingThreadsPendingMessageNone` | `ensureRunnable` only modifies scheduler, not objects | G3, G4, G5 |
| `removeRunnable_preserves_waitingThreadsPendingMessageNone` | `removeRunnable` only modifies scheduler, not objects | G4, G5 |

These are structural frame lemmas — the invariant speaks about TCB objects,
and operations that don't modify TCBs trivially preserve it. They follow the
same pattern as existing `*_preserves_ipcInvariant` frame lemmas in
`NotificationPreservation.lean`.

### 4.5. V3-G Complete File Change Summary

| File | Lines Added | Lines Modified | Type |
|------|-------------|----------------|------|
| `IPC/Invariant/Defs.lean` | ~20 | 3 (ipcInvariantFull def) | Definition + bundle update |
| `IPC/Invariant/NotificationPreservation.lean` | ~70-90 | 0 | Proofs (G2, G3) |
| `IPC/Invariant/EndpointPreservation.lean` | ~100-130 | 0 | Proofs (G4) |
| `IPC/Invariant/CallReplyRecv.lean` | ~80-120 | 0 | Proofs (G5) |
| `IPC/Invariant/Structural.lean` | ~40-60 | ~10-20 | Frame lemmas + bundle updates (G6) |
| `Capability/Invariant/Preservation.lean` | ~15 | ~10 | Extractor + lifecycle (G6) |
| `Architecture/Invariant.lean` | 0 | ~5 | Path fixes if needed (G6) |
| **Total** | **~325-435** | **~28-38** | |

---

## 5. Cross-Cutting Concerns

### 5.1. Interaction Between V3-E and V3-G

V3-E and V3-G modify different parts of the invariant hierarchy:
- V3-E adds proofs about `capabilityInvariantBundle` (capability subsystem)
- V3-G adds a predicate to `ipcInvariantFull` (IPC subsystem)

Both are composed into `coreIpcInvariantBundle`:
```lean
def coreIpcInvariantBundle (st : SystemState) : Prop :=
  schedulerInvariantBundle st ∧ capabilityInvariantBundle st ∧ ipcInvariantFull st
```

**Interaction point**: V3-G6 changes `ipcInvariantFull`, which changes
`coreIpcInvariantBundle`, which changes the destructuring paths used by V3-E's
`ipcUnwrapCaps_preserves_capabilityInvariantBundle` when it needs to extract
sub-components.

**Resolution**: V3-E operates at the `capabilityInvariantBundle` level, not
the `coreIpcInvariantBundle` level. V3-E's theorems take
`capabilityInvariantBundle st` as a hypothesis and prove
`capabilityInvariantBundle st'`. They do NOT directly construct or decompose
`ipcInvariantFull`. Therefore, V3-E and V3-G are **structurally independent**
at the proof level.

The only shared dependency is at the bundle composition layer (V3-G6 step 4),
where `coreIpcInvariantBundle` reconstruction must include both the V3-E
capability proof and the V3-G pending-message proof. This is a composition
task, not a conflict.

**Recommendation**: Implement V3-E first (no bundle changes needed), then
V3-G (bundle changes in G6). This ordering minimizes merge conflicts and
allows V3-E to be validated independently.

### 5.2. `private` Theorem Visibility

V3-E4 creates a `private` loop theorem in `Preservation.lean` that references
`ipcUnwrapCapsLoop` from `CapTransfer.lean`. After V3-E1 removes `private`
from the loop function, the theorem can reference it across module boundaries.

However, `Preservation.lean` already imports `CapTransfer.lean` transitively
(via `Capability/Operations.lean` → `IPC/Operations.lean`). The import chain
must be verified:

```
Preservation.lean
  → imports Capability/Invariant/Defs.lean
  → which imports ... → IPC/Operations/CapTransfer.lean (?)
```

If `CapTransfer.lean` is not in the import chain, V3-E4 will need an explicit
import addition. This is a small mechanical change but must be verified.

### 5.3. Precondition Propagation for V3-G2

The `notificationWait` preservation proof (V3-G2) requires knowing that the
thread entering the wait has `pendingMessage = none`. This fact must come from
one of:

1. **The caller's context**: `endpointReceiveDual` or the syscall dispatch
   layer knows the thread is `.ready` and has no pending message.
2. **A broader invariant**: If we prove that all `.ready` threads have
   `pendingMessage = none`, V3-G2 follows trivially.
3. **An explicit precondition**: Add `hPre : tcb.pendingMessage = none` to
   `notificationWait_preserves_waitingThreadsPendingMessageNone`.

**Recommended approach**: Option 3 (explicit precondition). This is the most
modular — it doesn't require proving a new global invariant about `.ready`
threads, and the precondition can be discharged at the call site from the
operation's context (the thread is executing a syscall, so it has already been
dispatched and its pending message consumed).

If a broader invariant about `.ready` threads is later desired (it would
strengthen the proof surface), it can be added as a separate V3 sub-task
without modifying V3-G2.

---

## 6. Execution Order & Dependency Graph

### 6.1. Dependency DAG

```
V3-E1 (expose loop)
  │
  ├── V3-E2 (loop invariant def)
  │     │
  │     ├── V3-E3 (base case)
  │     │     │
  │     │     └── V3-E4 (inductive step) ←── auxiliary CDT lemmas
  │     │           │
  │     │           └── V3-E5 (compose full theorem)
  │     │
  │     └── [auxiliary CDT lemmas: cdtCompleteness, cdtAcyclicity, slotCountBounded]
  │
  V3-G1 (define predicate)
  │
  ├── V3-G2 (notificationWait) ──────────────────┐
  ├── V3-G3 (notificationSignal) ────────────────┤
  ├── V3-G4 (endpointSend/Receive) ─────────────┤
  │     ↑                                        │
  │     └── [shared frame lemmas]                │
  ├── V3-G5 (endpointCall/ReplyRecv) ───────────┤
  │     ↑                                        │
  │     └── depends on V3-G4 primitives          │
  │                                               │
  └───────────────────────────────────────────────┘
                      │
                V3-G6 (bundle integration)
                      │
                      ↓
              [V3-K: endpointQueueNoDup — future task]
```

### 6.2. Recommended Execution Phases

**Phase A: Foundation (V3-E1 + V3-G1 + shared lemmas)**
- V3-E1: Remove `private` from `ipcUnwrapCapsLoop` (~5 min)
- V3-G1: Define `waitingThreadsPendingMessageNone` (~15 min)
- V3-G shared frame lemmas: `storeObject_preserves_*`, `ensureRunnable_preserves_*` (~30 min)
- **Gate**: `lake build` succeeds for modified modules

**Phase B: V3-E Proof Chain (sequential)**
- V3-E2: Loop invariant definition (~15 min)
- V3-E auxiliary lemmas: CDT preservation for `ipcTransferSingleCap` (~45 min)
- V3-E3: Base case proof (~15 min)
- V3-E4: Inductive step proof (~2-3 hours — main proof effort)
- V3-E5: Full composition (~30 min)
- **Gate**: `lake build SeLe4n.Kernel.Capability.Invariant.Preservation` succeeds

**Phase C: V3-G Per-Operation Proofs (parallelizable within phase)**
- V3-G2: `notificationWait` preservation (~30 min)
- V3-G3: `notificationSignal` preservation (~45 min)
- V3-G4: `endpointSend`/`endpointReceive` preservation (~1.5-2 hours)
- V3-G5: `endpointCall`/`endpointReplyRecv` preservation (~1.5-2 hours)
- **Gate**: Individual module builds succeed

**Phase D: Integration (V3-G6)**
- Update `ipcInvariantFull` definition (~5 min)
- Fix extractor theorem paths (~15 min)
- Update bundle-level preservation theorems in `Structural.lean` (~45 min)
- Update `lifecycleRetypeObject_preserves_coreIpcInvariantBundle` (~15 min)
- Audit `Architecture/Invariant.lean` for path breakage (~15 min)
- **Gate**: Full `lake build` succeeds; `test_full.sh` green

**Phase E: Validation & Documentation**
- Run `test_full.sh` (~10 min)
- Update documentation (see Section 9)
- **Gate**: All tests pass; no `sorry`; docs synchronized

### 6.3. Parallelization Opportunities

| Can Parallelize | Cannot Parallelize |
|-----------------|-------------------|
| V3-E1 ∥ V3-G1 (different files) | V3-E3 → V3-E4 → V3-E5 (sequential proof chain) |
| V3-G2 ∥ V3-G3 (different operations, same file — use separate regions) | V3-G5 depends on V3-G4 primitives |
| Phase B ∥ Phase C (V3-E and V3-G are structurally independent) | V3-G6 depends on all of V3-G2-G5 |

**Maximum parallelism**: Run Phase B (V3-E chain) and Phase C (V3-G per-op
proofs) concurrently. They modify disjoint files except `Preservation.lean`
(V3-E) and `Defs.lean` (V3-G1), which are in different regions.

---

## 7. Risk Assessment & Mitigations

### 7.1. Risk Matrix

| ID | Risk | Probability | Impact | Mitigation |
|----|------|-------------|--------|------------|
| R1 | V3-E4 CDT circularity: per-step theorem requires `hCdtPost` as hypothesis, creating apparent circular dependency | Medium | High | Prove standalone CDT preservation lemmas (Approach A in Section 3.3) |
| R2 | V3-E1 `private` removal causes naming collision | Low | Low | Rename to `ipcUnwrapCapsLoopImpl` if needed |
| R3 | V3-G2 precondition (`pendingMessage = none` for entering thread) not available at call site | Medium | Medium | Use explicit precondition (Option 3 in Section 5.3); discharge from dispatch context |
| R4 | V3-G6 bundle change breaks downstream proofs beyond identified extractors | Medium | Medium | Full `lake build` after bundle change; search for all `ipcInvariantFull` destructuring patterns |
| R5 | V3-E4 proof complexity exceeds estimate due to Lean 4 tactic behavior with nested fuel induction | Low-Medium | Medium | Follow existing proof template exactly; if tactics diverge, use `show` annotations to guide unification |
| R6 | V3-G4 endpoint operations have complex case splits that multiply proof obligations | Medium | Low | Reuse frame lemma infrastructure; factor common patterns into shared helpers |
| R7 | Import cycle when `Preservation.lean` needs `CapTransfer.lean` | Low | Low | Verify import chain; add explicit import if needed |

### 7.2. Highest-Risk Item: V3-E4 CDT Postcondition Threading

The per-step theorem signature:
```lean
theorem ipcTransferSingleCap_preserves_capabilityInvariantBundle
    ...
    (hCdtPost : cdtCompleteness st' ∧ cdtAcyclicity st') ...
```

requires CDT invariants of the *post-state* as a *precondition*. In the loop
induction, each step's post-state is the next step's pre-state. The CDT
invariants must be available at each intermediate state.

**Mitigation plan**:
1. **First attempt**: Extract CDT invariants from `capabilityInvariantBundle stNext`
   (which the per-step theorem proves). Since `capabilityInvariantBundle`
   includes `cdtCompleteness` and `cdtAcyclicity` as components, the CDT
   invariants for `stNext` can be extracted from the theorem's *output* and
   fed into the next step's `hCdtPost`. This is well-founded because the
   per-step theorem proves the full bundle, which includes CDT, which provides
   the hypothesis for the next step.

2. **Fallback**: If the above creates a unification issue (Lean cannot
   resolve the circular extraction), prove:
   ```lean
   theorem ipcTransferSingleCap_preserves_cdtCompleteness ...
   theorem ipcTransferSingleCap_preserves_cdtAcyclicity ...
   ```
   as standalone lemmas that do NOT depend on the full bundle proof. These
   can be derived directly from the component operations (`ensureCdtNodeForSlot`
   + `addEdge` preserve CDT structure).

---

## 8. Testing & Validation Strategy

### 8.1. Per-Sub-Task Validation

Every sub-task must pass its module build before proceeding:

| Sub-Task | Build Command |
|----------|--------------|
| V3-E1 | `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Operations.CapTransfer` |
| V3-E2-E5 | `source ~/.elan/env && lake build SeLe4n.Kernel.Capability.Invariant.Preservation` |
| V3-G1, V3-G6 (Defs) | `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Invariant.Defs` |
| V3-G2, V3-G3 | `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Invariant.NotificationPreservation` |
| V3-G4 | `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Invariant.EndpointPreservation` |
| V3-G5 | `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Invariant.CallReplyRecv` |
| V3-G6 (Structural) | `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Invariant.Structural` |
| V3-G6 (Preservation) | `source ~/.elan/env && lake build SeLe4n.Kernel.Capability.Invariant.Preservation` |
| V3-G6 (Architecture) | `source ~/.elan/env && lake build SeLe4n.Kernel.Architecture.Invariant` |

### 8.2. Integration Validation

After all sub-tasks complete:

```bash
# Tier 0+1: Hygiene + full build
./scripts/test_fast.sh

# Tier 0-2: + trace + negative-state
./scripts/test_smoke.sh

# Tier 0-3: + invariant surface anchors (REQUIRED for theorem changes)
./scripts/test_full.sh
```

### 8.3. Proof Hygiene Checks

```bash
# Zero sorry check
grep -r "sorry" SeLe4n/ --include="*.lean" | grep -v "^--" | grep -v "doc"

# Zero axiom check (excluding Lean builtins)
grep -r "axiom " SeLe4n/ --include="*.lean" | grep -v "^--"

# Invariant surface anchor check (test_tier3)
./scripts/test_tier3_invariant_surface.sh
```

### 8.4. Regression Safety

The trace harness (`lake exe sele4n`) and expected output fixture
(`tests/fixtures/main_trace_smoke.expected`) should be unaffected — no runtime
code changes. Verify with:

```bash
lake exe sele4n > /tmp/trace_output.txt 2>&1
diff tests/fixtures/main_trace_smoke.expected /tmp/trace_output.txt
```

---

## 9. Documentation Synchronization

Per CLAUDE.md documentation rules, the following must be updated in the same PR:

| Document | Update Required |
|----------|----------------|
| `docs/WORKSTREAM_HISTORY.md` | Mark V3-E and V3-G as complete; update V3 phase progress |
| `docs/spec/SELE4N_SPEC.md` | Update proof coverage table for IPC cap transfer and pending-message invariant |
| `docs/CLAIM_EVIDENCE_INDEX.md` | Add evidence entries for new theorems |
| `docs/DEVELOPMENT.md` | Update invariant bundle description if architecture section references `ipcInvariantFull` |
| `docs/gitbook/12-proof-and-invariant-map.md` | Add `waitingThreadsPendingMessageNone` to invariant map; update `ipcUnwrapCaps` proof status |
| `docs/codebase_map.json` | Regenerate (Lean sources changed) |
| `CHANGELOG.md` | Add V3-E and V3-G entries under next version |

### 9.1. CHANGELOG Entry Template

```markdown
## [v0.22.X] - YYYY-MM-DD

### Added
- **V3-E/M-PRF-2**: Complete loop composition proof for `ipcUnwrapCaps`
  with `Grant=true`. Fuel-indexed induction over `ipcUnwrapCapsLoop`
  threading `capabilityInvariantBundle` preservation through each cap transfer
  step. Closes the last proof gap in IPC capability transfer.
- **V3-G/M-PRF-5**: New `waitingThreadsPendingMessageNone` invariant ensuring
  threads in `blockedOnReceive` or `blockedOnNotification` states have
  `pendingMessage = none`. Proved preservation through all IPC operations
  (endpoint send/receive, call/reply/replyRecv, notification signal/wait).
  Integrated into `ipcInvariantFull` and all bundle-level theorems.
```

---

## Appendix A: Complete Sub-Task Registry

| ID | Finding | Task Summary | File(s) | Scope | Depends On |
|----|---------|-------------|---------|-------|------------|
| V3-E1 | M-PRF-2 | Remove `private` from `ipcUnwrapCapsLoop` | `CapTransfer.lean` | S | — |
| V3-E2 | M-PRF-2 | Define `ipcUnwrapCapsLoop_invariant` predicate | `Preservation.lean` | S | V3-E1 |
| V3-E-aux | M-PRF-2 | CDT preservation lemmas for `ipcTransferSingleCap` | `Preservation.lean` | S | — |
| V3-E3 | M-PRF-2 | Prove loop base case (fuel=0 / idx≥size) | `Preservation.lean` | S | V3-E2 |
| V3-E4 | M-PRF-2 | Prove loop inductive step (threading hSlotCap + hCdtPost) | `Preservation.lean` | M | V3-E3, V3-E-aux |
| V3-E5 | M-PRF-2 | Compose `ipcUnwrapCaps_preserves_capabilityInvariantBundle` | `Preservation.lean` | M | V3-E4 |
| V3-G1 | M-PRF-5 | Define `waitingThreadsPendingMessageNone` | `Defs.lean` | S | — |
| V3-G-infra | M-PRF-5 | Shared frame lemmas (storeObject, ensureRunnable, etc.) | `Structural.lean` | S | V3-G1 |
| V3-G2 | M-PRF-5 | Preservation for `notificationWait` | `NotificationPreservation.lean` | S | V3-G1, V3-G-infra |
| V3-G3 | M-PRF-5 | Preservation for `notificationSignal` (wake + merge) | `NotificationPreservation.lean` | S | V3-G1, V3-G-infra |
| V3-G4 | M-PRF-5 | Preservation for `endpointSend`/`endpointReceive` | `EndpointPreservation.lean` | M | V3-G1, V3-G-infra |
| V3-G5 | M-PRF-5 | Preservation for `endpointCall`/`endpointReplyRecv` | `CallReplyRecv.lean` | M | V3-G4 |
| V3-G6 | M-PRF-5 | Integrate into `ipcInvariantFull` + update all bundle theorems | `Defs.lean`, `Structural.lean`, `Preservation.lean` | S | V3-G2-G5 |

**Total sub-tasks**: 13 (6 Small, 5 Medium, 2 Infrastructure)
**Total estimated new Lean proof lines**: ~505-655
**Total estimated modified lines**: ~29-39
**Files touched**: 8
