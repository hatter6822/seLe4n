# seLe4n Full Codebase Audit Report

**Date**: 2026-02-23
**Version**: 0.11.6
**Toolchain**: Lean 4.27.0 / Lake 0.11.6
**Scope**: End-to-end review of all source, proofs, tests, and documentation

---

## Executive Summary

seLe4n is a Lean 4 formalization of core seL4 microkernel semantics producing
machine-checked proofs of invariant preservation. The codebase is **9,041 lines**
of Lean across 28 source modules, 3 test executables, and 16 shell scripts.

**Key metrics:**
- **271 theorems** across 21 modules — all fully proved
- **0 sorry / 0 axiom / 0 native_decide** — no proof escape hatches
- **0 unsafe / 0 noncomputable / 0 implemented_by** — entirely within Lean's safe kernel
- **69 type definitions** (structures, inductives, abbreviations)
- **262 function definitions** across 30 files
- **4 executable targets** (main trace, negative suite, IF suite, trace probe)

The proof surface is genuine: every theorem is constructively proved within Lean's
type theory. The invariant preservation chain composes cleanly from M1 (scheduler)
through M6 (architecture boundary). The information-flow model provides two-level
confidentiality/integrity labels with projection-based non-interference theorems.

However, there are significant semantic gaps between this model and actual seL4.
These gaps are documented below with severity ratings and recommended fixes.

---

## 1. Proof Integrity Assessment

### 1.1 Soundness verification

| Check | Result |
|-------|--------|
| `sorry` in any `.lean` file | **0 occurrences** |
| `axiom` in any `.lean` file | **0 occurrences** |
| `native_decide` in any `.lean` file | **0 occurrences** |
| `unsafe` in any `.lean` file | **0 occurrences** |
| `noncomputable` in any `.lean` file | **0 occurrences** |
| `implemented_by` in any `.lean` file | **0 occurrences** |
| `Decidable` instances | 6 occurrences in Architecture boundary contracts (legitimate) |
| Build status | **62/62 jobs succeed** |

This is a clean proof surface. All 271 theorems are constructively proved.

### 1.2 Invariant composition chain

The proof architecture composes subsystem invariants into progressively stronger
bundles. Each level's preservation is proved over all operations at that level:

```
M1: schedulerInvariantBundle
     = queueCurrentConsistent ∧ runQueueUnique ∧ currentThreadValid

M2: capabilityInvariantBundle
     = cspaceSlotUnique ∧ cspaceLookupSound
       ∧ cspaceAttenuationRule ∧ lifecycleAuthorityMonotonicity

M3: m3IpcSeedInvariantBundle
     = schedulerInvariantBundle ∧ capabilityInvariantBundle ∧ ipcInvariant

M3.5: m35IpcSchedulerInvariantBundle
       = m3IpcSeedInvariantBundle ∧ ipcSchedulerCoherenceComponent

M4-A: m4aLifecycleInvariantBundle
       = m35IpcSchedulerInvariantBundle ∧ lifecycleInvariantBundle

M5: serviceLifecycleCapabilityInvariantBundle
     (service + lifecycle + capability composition)

M6: proofLayerInvariantBundle
     = schedulerInvariantBundle ∧ capabilityInvariantBundle
       ∧ m3IpcSeedInvariantBundle ∧ m35IpcSchedulerInvariantBundle
       ∧ lifecycleInvariantBundle ∧ serviceLifecycleCapabilityInvariantBundle
```

Each level is preserved by all operations at its scope. The chain is complete
and no level's preservation depends on unproved assumptions (except the
`AdapterProofHooks` at M6 — see finding C-09).

### 1.3 Theorem classification

Not all 271 theorems carry equal weight. The codebase's own F-16 classification
identifies three categories:

| Category | Count | Assurance level |
|----------|-------|-----------------|
| Substantive preservation (state changes, invariant restored) | ~145 | High |
| Structural/functional lemmas (round-trips, decompositions) | ~80 | High |
| Error-case preservation (trivially `intro hInv; exact hInv`) | ~46 | None — padding |

The ~46 error-case theorems are trivially true because error paths return the
pre-state unchanged. They inflate the theorem count without providing security
evidence. **Recommendation**: tag these with a `@[trivial_preservation]` attribute
or move them to a clearly labeled section so consumers can discount them.

---

## 2. High-Severity Findings

### C-01: No Untyped memory objects — lifecycle model diverges from seL4

**Location**: `SeLe4n/Model/Object.lean:389-395`
**Severity**: High

`KernelObject` has 5 variants: `tcb`, `endpoint`, `notification`, `cnode`,
`vspaceRoot`. seL4's critical sixth object type — **Untyped** — is absent.

In seL4, all memory allocation flows through Untyped Retype: an untyped region
is split into typed objects. This is the foundation of seL4's spatial isolation
guarantee. Without Untyped objects:

- `lifecycleRetypeObject` performs in-place type mutation of existing objects,
  which has no seL4 counterpart. Real retype creates *new* objects from untyped
  memory; it never transmutes an endpoint into a TCB.
- There is no notion of "free memory" or allocation tracking.
- The capability derivation tree (untyped → typed children) cannot be modeled,
  which means full revoke (revoking all capabilities derived from an untyped)
  is structurally impossible.

**Impact**: Claims about modeling seL4 lifecycle semantics are overstated.
The `lifecycleRetypeObject` operation is a useful abstraction for testing
invariant preservation over object-store mutations, but it does not correspond
to any real seL4 operation.

**Recommendation**: Introduce an `untyped` variant to `KernelObject` with a
region-size field. Redefine `lifecycleRetypeObject` as creating a new object
from an untyped region (reducing the untyped's remaining capacity), not
transmuting an existing object. Add a `retypeAuthority` invariant proving
that retype never exceeds the parent untyped's capacity.

### C-02: API.lean contains zero definitions

**Location**: `SeLe4n/Kernel/API.lean` (22 lines, all imports)
**Severity**: High

The file documented as the "public kernel interface" is purely an import
aggregator. It contains no definitions, no type signatures, no access control.
Any consumer can call any internal function from any subsystem.

This means:
- There is no defined public API surface for the kernel model.
- Internal helpers like `chooseBestRunnable`, `rotateCurrentToBack`,
  `storeTcbIpcState` are as accessible as `schedule` or `endpointSend`.
- Documentation claiming a "public kernel interface" is misleading.

**Recommendation**: Define an explicit API surface in `API.lean` that re-exports
only the intended public operations. Mark internal helpers as `private` or move
them to `Private` sub-namespaces. This also enables a test that verifies the
public API hasn't accidentally grown.

### C-03: Non-interference proofs require identical operations on both states

**Location**: `SeLe4n/Kernel/InformationFlow/Invariant.lean`
**Severity**: High

All five non-interference theorems follow this pattern:

```lean
theorem op_preserves_lowEquivalent
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hStep₁ : op s₁ = .ok ((), s₁'))
    (hStep₂ : op s₂ = .ok ((), s₂'))
    : lowEquivalent ctx observer s₁' s₂'
```

Both states execute the **same** operation with the **same** parameters. This
proves "step consistency" — a necessary but insufficient condition for non-
interference. True non-interference (as established in the seL4 infoflow proof)
requires showing that a low observer cannot distinguish states regardless of
what the high-domain thread does, including executing *different* operations.

The current model cannot express the statement "for all high-domain operations
`op_h`, if `lowEquivalent s₁ s₂` and `op_h s₁ = .ok s₁'`, then
`lowEquivalent s₁' s₂`" because `op_h` may affect objects that `s₂` doesn't
have in the same configuration.

**Impact**: The non-interference proofs provide useful but incomplete security
evidence. They do not establish the classical Goguen-Meseguer non-interference
property that seL4's infoflow proof targets.

**Recommendation**: State the limitation explicitly in the module docstring.
Consider adding a "high-step unwinding" theorem that shows any high-domain
operation on `s₁` alone preserves `lowEquivalent s₁' s₂` (the one-sided
unwinding condition). This is the missing piece for full non-interference.

### C-04: Endpoint send-receive handshake is incomplete

**Location**: `SeLe4n/Kernel/IPC/Operations.lean:44-49`
**Severity**: High

When `endpointSend` encounters an endpoint in `receive` state with a waiting
receiver:
```lean
| .receive =>
    match ep.queue, ep.waitingReceiver with
    | [], some _ =>
        let ep' := { state := .idle, queue := [], waitingReceiver := none }
        storeObject endpointId (.endpoint ep') st
    | _, _ => .error .endpointStateMismatch
```

The operation transitions the endpoint to idle and drops the waiting receiver,
but:
- The sender's message is never delivered to the receiver.
- Neither the sender's nor the receiver's `TCB.ipcState` is updated.
- The receiver is not added back to the runnable queue.
- The sender is not blocked or completed.

In seL4, a send-to-waiting-receiver completes synchronously: the message is
transferred, the receiver is unblocked, and both threads' states are updated.
The current model simply discards the receiver.

**Impact**: The IPC handshake path cannot demonstrate that message delivery
preserves scheduler or capability invariants, because no delivery occurs.

**Recommendation**: Update the send-to-receive path to:
1. Update receiver's `ipcState` to `.ready`
2. Add receiver back to runnable queue via `ensureRunnable`
3. Optionally model message content transfer (or document omission)

### C-05: Service graph is external to the capability system

**Location**: `SeLe4n/Model/State.lean:70` (services field)
**Severity**: High

`SystemState.services : ServiceId → Option ServiceGraphEntry` is populated
via `storeServiceEntry` and has no formal connection to the capability graph.
There is no theorem proving that a service's existence, dependencies, or
status reflects actual capability-based authority relationships.

In seL4, services don't exist as first-class kernel objects — authority
relationships are derived from the capability graph. The seLe4n service model
is an overlay that must be manually kept consistent with the underlying
capability state.

**Impact**: Service invariant preservation theorems prove that service
operations maintain service-graph consistency, but this consistency has no
grounding in capability authority. A service could declare dependencies and
isolation constraints that contradict the actual capability structure.

**Recommendation**: Add a `serviceGraphConsistentWithCapabilities` invariant
that ties service entries to underlying capability-store state. At minimum,
prove that a service's `backingObject` exists in the object store.

---

## 3. Medium-Severity Findings

### C-06: Flat VSpace model cannot reason about page-table structure

**Location**: `SeLe4n/Model/Object.lean:112-115`
**Severity**: Medium

VSpace is modeled as `List (VAddr × PAddr)` — a flat mapping list. seL4 uses
hierarchical multi-level page tables (2-4 levels depending on architecture).
The flat model cannot express:

- Page table walk semantics or intermediate-level permissions
- Large page / super-section mappings
- Page table object capabilities (Frame, PageTable, ASID Pool)
- Guard-bit or level-specific translation invariants

The `VSpaceRoot.noVirtualOverlap` invariant and the round-trip theorems
(`vspaceLookup_after_map`, etc.) are meaningful for the flat abstraction but
do not extend to hierarchical page tables.

**Recommendation**: This is an acceptable simplification if explicitly scoped.
Document in SELE4N_SPEC.md that the VSpace model covers "single-level
deterministic lookup" and cannot be used to reason about multi-level page
table invariants. Consider adding a `FlatVSpaceDisclaimer` doc-anchor.

### C-07: Scheduler ignores domain-based scheduling

**Location**: `SeLe4n/Kernel/Scheduler/Operations.lean:7-22`
**Severity**: Medium

`chooseBestRunnable` selects the highest-priority thread from a flat runnable
queue. `TCB.domain` exists but is never consulted during scheduling. seL4
uses a domain-based scheduler where:

- Time is divided into domain timeslots
- Only threads in the current domain can run during its timeslot
- Domain scheduling provides temporal isolation

The current model provides no temporal isolation guarantees. Two threads in
different domains with different priorities will simply be scheduled by
priority, not by domain assignment.

**Recommendation**: Add a `currentDomain` field to `SchedulerState` and
filter `runnable` by domain before priority selection. Add a
`domainIsolation` invariant proving threads only run in their assigned
domain's timeslot.

### C-08: No Frame/PageTable capabilities

**Location**: `SeLe4n/Kernel/Architecture/VSpace.lean:28-47`
**Severity**: Medium

VSpace operations (`vspaceMapPage`, `vspaceUnmapPage`, `vspaceLookup`) are
authorized by ASID resolution, not by capability possession. There are no
Frame or PageTable kernel objects or capabilities.

In seL4, mapping a page requires:
1. A Frame capability (authority to use the physical memory)
2. A VSpace/PageTable capability (authority to modify the address space)
3. An ASID Pool capability (authority over the address space identifier)

The current model skips all three authority checks. Any caller who knows the
ASID can map arbitrary physical addresses into the address space.

**Recommendation**: Add capability-based authority checks to VSpace
operations. At minimum, require a capability with the target VSpace root
as target and `write` rights.

### C-09: AdapterProofHooks are assumed, not proved

**Location**: `SeLe4n/Kernel/Architecture/Invariant.lean:44-61`
**Severity**: Medium

The `AdapterProofHooks` structure requires callers to provide invariant
preservation proofs for adapter transitions:

```lean
structure AdapterProofHooks (contract : RuntimeBoundaryContract) where
  preserveAdvanceTimer : ∀ ticks st, proofLayerInvariantBundle st → ...
  preserveWriteRegister : ∀ reg value st, proofLayerInvariantBundle st → ...
  preserveReadMemory : ∀ addr st, proofLayerInvariantBundle st → ...
```

These obligations are parameters, not theorems. The M6 preservation theorems
are therefore conditional: they hold *if* someone provides valid
`AdapterProofHooks`. No concrete instance of `AdapterProofHooks` is
constructed anywhere in the codebase.

**Impact**: The architecture boundary preservation chain has an open
assumption. The theorems are structurally sound but not grounded.

**Recommendation**: Construct at least one concrete `AdapterProofHooks`
instance (e.g., for the test fixture's `RuntimeBoundaryContract`) and prove
its preservation obligations. This closes the assumption gap for at least one
configuration.

### C-10: `storeTcbIpcState` silently succeeds on missing TCBs

**Location**: `SeLe4n/Kernel/IPC/Operations.lean:24-30`
**Severity**: Medium

```lean
def storeTcbIpcState ... : Except KernelError SystemState :=
  match lookupTcb st tid with
  | none => .ok st    -- ← silently succeeds
  | some tcb => ...
```

When the target thread doesn't exist (or isn't a TCB), the function returns
success with the state unchanged. This means operations that depend on TCB
state updates (notification wake, notification wait blocking) will silently
skip the TCB update if the thread ID is invalid.

Callers like `notificationSignal` chain through `storeTcbIpcState` to wake
a thread. If the thread doesn't exist, the wake appears to succeed but the
thread's IPC state is never updated.

**Recommendation**: Return `.error .objectNotFound` when the TCB doesn't
exist, or add a theorem proving that callers always pass valid thread IDs.

### C-11: `ensureRunnable` lacks `runQueueUnique` preservation proof

**Location**: `SeLe4n/Kernel/IPC/Operations.lean:13-17`
**Severity**: Medium

```lean
def ensureRunnable (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  if tid ∈ st.scheduler.runnable then st
  else { st with scheduler := { st.scheduler with
    runnable := st.scheduler.runnable ++ [tid] } }
```

The `if` guard prevents duplicates, but there is no theorem proving that
`ensureRunnable` preserves `runQueueUnique`. This function is called by
`notificationSignal` to add a woken thread to the runnable queue. Without
the preservation theorem, the scheduler invariant chain has a gap at the
IPC/scheduler boundary.

**Recommendation**: Prove `ensureRunnable_preserves_runQueueUnique`.

### C-12: Service BFS fuel bound is heuristic

**Location**: `SeLe4n/Kernel/Service/Operations.lean:96-97`
**Severity**: Medium

```lean
def serviceBfsFuel (st : SystemState) : Nat :=
  st.objectIndex.length + 256
```

The BFS cycle-detection fuel is `objectIndex.length + 256`. If the service
graph has more than this many distinct service nodes (service IDs that don't
correspond to kernel objects), the BFS may exhaust fuel before finding a
cycle and conservatively allow the edge — potentially creating an undetected
cycle.

No theorem proves this bound is sufficient for the actual service graph size.

**Recommendation**: Either prove a bound sufficiency theorem, or compute
fuel from the actual service count (`services` field) rather than
`objectIndex`.

---

## 4. Low-Severity Findings

### C-13: No CI configuration

No `.github/workflows/` files exist. The build/test pipeline relies on shell
scripts (`test_fast.sh`, `test_smoke.sh`, `test_full.sh`) with no automated
CI integration. PRs can merge without running any validation.

**Recommendation**: Add a CI workflow that runs at least `test_smoke.sh`.

### C-14: Error-case preservation theorems inflate proof count

~46 of the 271 theorems are trivially `intro hInv; exact hInv` because the
error path returns the pre-state unchanged. These are documented via F-16
but still appear in theorem counts and CLAIM_EVIDENCE_INDEX without
qualification.

**Recommendation**: Add a `@[trivial_preservation]` attribute or separate
these into a distinct count in documentation.

### C-15: Redundant imports in root module

`SeLe4n.lean` imports `Architecture.*` and `InformationFlow.Enforcement`
directly, but these are already transitively available through
`Kernel.API`. Harmless but adds maintenance burden.

### C-16: Badge OR-accumulation lacks algebraic theorems

`notificationSignal` uses `existing.toNat ||| badge.toNat` for badge
merging. No commutativity or associativity theorems exist for the merged
badge value, making it impossible to formally reason about badge
accumulation order independence.

### C-17: No global ASID coherence

Each `VSpaceRoot` carries its own `asid` field, and
`vspaceAsidRootsUnique` enforces uniqueness. But there is no global ASID
table or pool. ASID allocation and deallocation are not modeled, meaning
ASID reuse scenarios cannot be analyzed.

---

## 5. Architecture and Design Strengths

The following design decisions are well-executed:

1. **Typed identifiers** (`Prelude.lean`): 12 distinct wrapper types
   (`ObjId`, `ThreadId`, `CPtr`, `Slot`, etc.) prevent category errors at
   compile time. The explicit `ofNat`/`toNat` helpers enforce conscious
   conversion.

2. **Deterministic error monad** (`KernelM`): All transitions return
   `Except KernelError (α × SystemState)`. No non-determinism, no silent
   failures (except C-10 above). Error variants are well-chosen and
   cover major fault classes.

3. **Invariant/Operations split**: Every subsystem cleanly separates
   transition definitions (`Operations.lean`) from invariant statements
   and preservation proofs (`Invariant.lean`). This separation prevents
   circular dependencies and makes the proof architecture navigable.

4. **Capability attenuation safety** (F-06): The `mintDerivedCap` function
   ensures by construction that derived capabilities attenuate parent
   rights. The `mintDerivedCap_target_preserved_with_badge_override`
   theorem explicitly proves that badge parameters cannot escalate
   privilege — closing a real-world attack vector.

5. **VSpace round-trip theorems**: `vspaceLookup_after_map`,
   `vspaceLookup_after_unmap`, and their `_other` variants establish
   functional correctness of VSpace operations. These are substantive
   proofs that close TPI-001.

6. **Double-wait prevention** (F-12): `notificationWait` explicitly
   checks `waiter ∈ ntfn.waitingThreads` before appending, with a
   proved theorem (`notificationWait_error_alreadyWaiting`).

7. **Cycle detection** (F-07): `serviceRegisterDependency` uses bounded
   BFS to detect dependency cycles before insertion, with proved
   self-loop rejection.

8. **Testing depth**: The `NegativeStateSuite` (372 lines) exercises
   every error branch systematically. The `InformationFlowSuite` (300
   lines) tests non-tautological low-equivalence with distinct states.
   The trace fixture (`main_trace_smoke.expected`, 51 lines) provides
   deterministic regression anchoring.

---

## 6. Module-by-Module Summary

| Module | Lines | Theorems | Defs | Assessment |
|--------|-------|----------|------|------------|
| Prelude | 278 | 0 | 14 | Sound typed-identifier foundation |
| Machine | 50 | 0 | 8 | Clean pure-functional machine model |
| Model/Object | 421 | 13 | 31 | Good; missing Untyped (C-01) |
| Model/State | 497 | 25 | 30 | Comprehensive; service graph concern (C-05) |
| Scheduler/Invariant | 74 | 2 | 5 | Minimal invariant definitions |
| Scheduler/Operations | 416 | 23 | 5 | Complete; no domain scheduling (C-07) |
| Capability/Operations | 238 | 6 | 12 | F-06 badge safety proven |
| Capability/Invariant | 895 | 42 | 18 | Largest file; solid preservation chain |
| IPC/Operations | 353 | 6 | 9 | Handshake gap (C-04); storeTcbIpcState (C-10) |
| IPC/Invariant | 890 | 39 | 11 | Cross-subsystem composition |
| Lifecycle/Operations | 317 | 14 | 3 | In-place retype concern (C-01) |
| Lifecycle/Invariant | ~350 | 11 | 11 | M4-A preservation chain |
| Service/Operations | 265 | 8 | 8 | BFS cycle detection (C-12) |
| Service/Invariant | 470 | 32 | 14 | Heavy preservation surface |
| Architecture/Assumptions | 120 | 4 | 10 | Well-structured boundary contracts |
| Architecture/Adapter | 125 | 6 | 6 | Deterministic adapters |
| Architecture/VSpace | 162 | 3 | 6 | ASID resolution + round-trips |
| Architecture/VSpaceInvariant | 360 | 8 | 3 | Substantive map/unmap preservation |
| Architecture/Invariant | 162 | 7 | 2 | M6 composition (C-09 hooks gap) |
| InformationFlow/Policy | 114 | 6 | 9 | Two-level lattice, refl/trans proven |
| InformationFlow/Projection | 108 | 3 | 9 | Clean projection model |
| InformationFlow/Enforcement | 197 | 7 | 3 | Three checked operations |
| InformationFlow/Invariant | 315 | 6 | 1 | Non-interference (C-03 limitation) |

---

## 7. Testing Assessment

### 7.1 Test executables

| Executable | Purpose | Lines | Verdict |
|-----------|---------|-------|---------|
| `sele4n` (Main) | Trace harness — exercises all subsystems | 447 | Good regression anchor |
| `negative_state_suite` | Error-branch coverage | 372 | Thorough negative testing |
| `information_flow_suite` | IF policy + projection + enforcement | 300 | Non-tautological; F-04 fixes genuine |
| `trace_sequence_probe` | Deeper trace sequences | 163 | Supplementary coverage |

### 7.2 Test tier structure

| Tier | Script | What it validates |
|------|--------|-------------------|
| 0 | `test_tier0_hygiene.sh` | No sorry/axiom, shellcheck, file hygiene |
| 1 | `test_tier1_build.sh` | `lake build` succeeds |
| 2 | `test_tier2_trace.sh` + `test_tier2_negative.sh` | Trace fixture match + negative suite |
| 3 | `test_tier3_invariant_surface.sh` | Theorem name anchors exist in source |
| 4 | `test_tier4_nightly_candidates.sh` | Experimental/nightly checks |

### 7.3 Test gaps

- No property-based / fuzzing tests
- No mutation testing (injecting `sorry` to verify test detection)
- Trace fixture (`main_trace_smoke.expected`) is string-matched, so any
  change to `Repr` formatting breaks the test without semantic change
- No test for `AdapterProofHooks` instantiation (see C-09)

---

## 8. Recommended Priority Actions

| Priority | Finding | Action |
|----------|---------|--------|
| P0 | C-04 | Fix endpoint send-receive handshake to update TCB states |
| P0 | C-10 | Make `storeTcbIpcState` return error on missing TCB |
| P1 | C-01 | Document Untyped omission scope in spec; plan Untyped introduction |
| P1 | C-03 | Add one-sided unwinding theorem or document limitation |
| P1 | C-11 | Prove `ensureRunnable_preserves_runQueueUnique` |
| P1 | C-02 | Define explicit API surface in API.lean |
| P2 | C-09 | Construct concrete `AdapterProofHooks` instance |
| P2 | C-05 | Add service-graph/capability consistency invariant |
| P2 | C-13 | Add CI workflow |
| P3 | C-07 | Add domain-based scheduling |
| P3 | C-06 | Document flat VSpace scope limitation |
| P3 | C-12 | Prove BFS fuel sufficiency or fix fuel computation |

---

## 9. Conclusion

seLe4n is a well-structured formalization with genuinely clean proofs: zero
sorry, zero axiom, and a complete invariant preservation chain from scheduler
through architecture boundary. The code quality is high, the typed-identifier
discipline is excellent, and the testing infrastructure provides meaningful
regression coverage.

The primary concerns are semantic: the model omits seL4's Untyped memory
system, uses flat VSpace, ignores domain scheduling, and leaves the IPC
handshake incomplete. The non-interference proofs establish step-consistency
but not full Goguen-Meseguer non-interference. These gaps limit the model's
applicability to reasoning about the actual seL4 kernel.

For its stated scope — an abstract model producing machine-checked invariant
preservation proofs — the project delivers. The recommended actions above
would strengthen both the semantic fidelity and the proof surface.
