# 02 — Deep Codebase Audit (Code-First)

This document captures the implementation reality of TPI-D07 as determined by direct source code inspection. Every behavioral claim is traceable to specific line ranges in the repository.

---

## 1. Repository and development-state baseline

The seLe4n project is a **Lean 4 microkernel verification model**. The architecture is:

- **Kernel subsystems** split into paired `Operations.lean` / `Invariant.lean` modules across seven subsystems: `Architecture`, `Capability`, `IPC`, `Lifecycle`, `Scheduler`, `Service`, and `InformationFlow`.
- **Data model** in `SeLe4n/Model/` (`State.lean`, `Object.lean`) with typed ID wrappers in `SeLe4n/Prelude.lean`.
- **Tiered testing** across five levels (Tier 0 hygiene → Tier 4 nightly).
- **Portfolio status:** WS-D1 through WS-D4 completed. TPI-D07 is the **sole remaining proof debt** — all other tracked issues TPI-D01 through TPI-D06 are CLOSED.

---

## 2. Cycle-prevention operational logic

### 2.1 `serviceRegisterDependency` check ordering

Source: `Operations.lean:142–160`

The function enforces a **strict deterministic check ordering**:

| Step | Check | Code location | Failure result | Goal state after discharge |
|---|---|---|---|---|
| 1 | `lookupService st svcId` — source exists | `:145–146` | `.error .objectNotFound` | `Invariant.lean:370`: discharged by `simp [hSvc] at hReg` |
| 2 | `lookupService st depId` — target exists | `:148–149` | `.error .objectNotFound` | `Invariant.lean:374`: discharged by `simp [hDep] at hReg` |
| 3 | `svcId = depId` — self-dependency guard | `:151` | `.error .cyclicDependency` | `Invariant.lean:378`: discharged by `simp [hSelf] at hReg` |
| 4 | `depId ∈ svc.dependencies` — idempotent | `:153` | `.ok ((), st)` (no-op) | `Invariant.lean:382–384`: discharged by `exact hAcyc` |
| 5 | `serviceHasPathTo st depId svcId (serviceBfsFuel st)` — cycle detect | `:155` | `.error .cyclicDependency` | `Invariant.lean:387`: discharged by `simp [hCycle] at hReg` |
| 6 | Edge insertion | `:157–160` | `.ok ((), st')` | `Invariant.lean:394`: **`sorry` — this is TPI-D07** |

The post-state `st'` is produced by:
```lean
let svc' : ServiceGraphEntry := { svc with dependencies := svc.dependencies ++ [depId] }
storeServiceEntry svcId svc' st
```

Where `storeServiceEntry` (`Operations.lean:11–12`) unwraps to:
```lean
fun st => .ok ((), storeServiceState svcId svc' st)
```

And `storeServiceState` (`State.lean:168–172`) performs a function update:
```lean
{ st with services := fun sid' => if sid' = sid then some entry else st.services sid' }
```

### 2.2 Key observation: the `storeServiceEntry`/`storeServiceState` simplification

At `Invariant.lean:391–393`, the proof unfolds `storeServiceEntry` and simplifies:

```lean
unfold storeServiceEntry at hReg
simp at hReg
cases hReg
```

After `cases hReg`, the goal state becomes:

```
⊢ ¬ serviceHasPathTo
    (storeServiceState svcId { svc with dependencies := svc.dependencies ++ [depId] } st)
    sid sid
    (serviceBfsFuel (storeServiceState svcId { svc with dependencies := svc.dependencies ++ [depId] } st))
    = true
```

Note: `serviceBfsFuel` in the goal references the **post-state** (`st'`), not the pre-state. This is critical — the fuel computation `st'.objectIndex.length + 256` equals `st.objectIndex.length + 256` because `storeServiceState` does not modify `objectIndex`. This invariance must be established as a lemma.

---

## 3. Bounded BFS reachability (`serviceHasPathTo`)

Source: `Operations.lean:110–127`

### 3.1 Algorithm structure

```lean
def serviceHasPathTo
    (st : SystemState) (src target : ServiceId) (fuel : Nat) : Bool :=
  go [src] [] fuel
where
  go (frontier visited : List ServiceId) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
      match frontier with
      | [] => false
      | node :: rest =>
          if node = target then true
          else if node ∈ visited then go rest visited (fuel + 1)
          else
            let deps := match lookupService st node with
              | some svc => svc.dependencies
              | none => []
            let newFrontier := rest ++ deps.filter (· ∉ visited)
            go newFrontier (node :: visited) fuel
```

### 3.2 Behavioral properties (verified by code inspection)

| Property | Evidence | Proof relevance |
|---|---|---|
| **Fuel consumed only on distinct-node expansion** | The `else` branch (new node) calls `go ... fuel` (decrements by 1). The `node ∈ visited` branch calls `go ... (fuel + 1)` (recycles — passes the same value as the input). | The BFS explores at most `fuel` distinct nodes. |
| **Fuel bound** | `serviceBfsFuel st = st.objectIndex.length + 256` (`Operations.lean:96–97`) | Must dominate the number of distinct reachable services. |
| **Conservative on exhaustion** | Returns `false` when fuel hits 0. | False negatives are possible; false positives are not. |
| **Visited-set monotonicity** | Each expansion adds `node` to `visited`; visited is never shrunk. | Key loop-invariant property. |
| **Frontier evolution** | New node: `rest ++ deps.filter (· ∉ visited)`. Visited node: `rest`. Empty frontier: `false`. | The frontier is manipulated queue-style (BFS, not DFS). |

### 3.3 Termination analysis

Lean 4 must accept `go` as terminating. The pattern-match `| fuel + 1 =>` binds `fuel` to `n - 1` where `n` is the input. The two recursive calls are:

1. **Visited branch:** `go rest visited (fuel + 1)` — passes `n` (same as input). **Not structurally decreasing on `Nat`.**
2. **Expansion branch:** `go newFrontier (node :: visited) fuel` — passes `n - 1`. **Structurally decreasing on `Nat`.**

Since the visited branch does not decrease the `Nat` argument, Lean cannot use simple structural recursion on `Nat`. The function terminates because:

- In the visited branch, `frontier` strictly shrinks (`rest` is shorter than `node :: rest`).
- In the expansion branch, `fuel` strictly decreases.

Lean 4 likely accepts this via well-founded recursion on a **lexicographic measure** `(fuel, frontier.length)` or through the `where` clause's internal termination elaboration. The exact termination proof Lean generates is relevant to our BFS soundness proof — we may need to use `serviceHasPathTo.go.eq_def` or similar equational lemmas rather than attempting to unfold the definition directly.

### 3.4 `serviceBfsFuel` analysis

```lean
def serviceBfsFuel (st : SystemState) : Nat :=
  st.objectIndex.length + 256
```

The `objectIndex` field (`State.lean:48`) is a `List ObjId` that tracks kernel objects, **not services**. Services are tracked in the `services : ServiceId → Option ServiceGraphEntry` function field, which has an infinite domain (`ServiceId` is a `Nat` wrapper).

**Key question for fuel adequacy:** Does `st.objectIndex.length + 256` always exceed the number of distinct `ServiceId` values with `lookupService st sid ≠ none`?

This is **not guaranteed by the type system alone**. In practice, service registration is preceded by object creation (each service has a `backingObject : ObjId` that should be in the object index), but no formal invariant currently links the two. This is the core of [Risk R1](./05_RISK_REGISTER.md#risk-1).

---

## 4. Invariant definition and proof state

### 4.1 Acyclicity invariant

Source: `Invariant.lean:349–350`

```lean
def serviceDependencyAcyclic (st : SystemState) : Prop :=
  ∀ sid, ¬ serviceHasPathTo st sid sid (serviceBfsFuel st) = true
```

This defines acyclicity in terms of the **executable BFS**, not a declarative graph property. A cycle exists (from the invariant's perspective) if and only if the BFS reports self-reachability under the standard fuel bound.

### 4.2 Preservation theorem and `sorry` site

Source: `Invariant.lean:363–394`

The proof is structurally complete for all non-insertion branches. After case-splitting, the insertion branch reduces to:

```
Goal state at sorry (line 394):
  svcId depId : ServiceId
  st : SystemState
  svc : ServiceGraphEntry
  depSvc : ServiceGraphEntry
  hSvc : lookupService st svcId = some svc
  hDep : lookupService st depId = some depSvc
  hSelf : ¬ svcId = depId
  hExists : ¬ depId ∈ svc.dependencies
  hCycle : ¬ serviceHasPathTo st depId svcId (serviceBfsFuel st) = true
  hAcyc : serviceDependencyAcyclic st
  sid : ServiceId
  ⊢ ¬ serviceHasPathTo
      (storeServiceState svcId { svc with dependencies := svc.dependencies ++ [depId] } st)
      sid sid
      (serviceBfsFuel
        (storeServiceState svcId { svc with dependencies := svc.dependencies ++ [depId] } st))
      = true
```

**Critical observations about the goal:**

1. The goal quantifies over an **arbitrary** `sid` — not just `svcId` or `depId`. Any service must remain non-self-reachable.
2. The `serviceBfsFuel` argument references the **post-state**. Since `storeServiceState` only modifies `services` (not `objectIndex`), the fuel is unchanged: `serviceBfsFuel st' = serviceBfsFuel st`.
3. The hypothesis `hCycle` uses `¬ ... = true` rather than `... = false`. These are equivalent for `Bool` but may require `Bool.not_eq_true_iff_ne_true` or `decide` to convert.

### 4.3 Available hypotheses summary

| Hypothesis | Meaning | Proof utility |
|---|---|---|
| `hSvc` | Source service exists with entry `svc` | Grounds `serviceEdge st svcId depId` after insertion |
| `hDep` | Dependency target exists with entry `depSvc` | Needed for BFS fan-out at `depId` |
| `hSelf` | `svcId ≠ depId` | Prevents trivial self-cycle via new edge |
| `hExists` | `depId ∉ svc.dependencies` | The edge is genuinely new (not idempotent) |
| `hCycle` | BFS finds no path `depId → ... → svcId` | Core: adding `svcId → depId` won't create a cycle |
| `hAcyc` | Pre-state is acyclic (BFS-based definition) | Induction base for post-state acyclicity |

---

## 5. Executable evidence baseline

Source: `tests/NegativeStateSuite.lean:319–367`

### 5.1 Current test coverage

| Test case | Services | Expected result | Lines |
|---|---|---|---|
| Self-loop rejection | A → A | `.error .cyclicDependency` | 344–346 |
| Missing target rejection | A → 999 (nonexistent) | `.error .objectNotFound` | 349–352 |
| Successful registration | A → B | `.ok` (yields `svcStateAB`) | 355–358 |
| Cycle detection | B → A (after A→B) | `.error .cyclicDependency` | 360–362 |
| Idempotent re-registration | A → B (already present) | `.ok` | 364–365 |

### 5.2 Test fixture

Two services with IDs 100 and 101, both `stopped`, empty dependency lists, constructed via `BootstrapBuilder`:

```lean
let svcIdA : ServiceId := ⟨100⟩
let svcIdB : ServiceId := ⟨101⟩
```

### 5.3 Coverage gaps

The current suite exercises only **two-node** graphs. Missing topologies:

- **Chain length ≥ 3** — A→B→C, then attempt C→A (transitive cycle detection)
- **Diamond DAG** — A→B, A→C, B→D, C→D (multiple paths, visited-set correctness)
- **Positive deep insertion** — verify BFS is not over-restrictive on non-cyclic graphs
- **Fan-out stress** — a service with many dependencies to exercise fuel consumption

These gaps are addressed in [M4: Executable Evidence Expansion](./milestones/M4_EXECUTABLE_EVIDENCE.md).

---

## 6. Documentation-to-code consistency audit

| Document | TPI-D07 status | Accuracy vs. code |
|---|---|---|
| `AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md:214` | IN PROGRESS | Correct — `sorry` exists at line 394 |
| `AUDIT_v0.11.0_WORKSTREAM_PLAN.md:337` | WS-D4 completed, `sorry` tracked | Correct — partial completion acknowledged |
| `CLAIM_EVIDENCE_INDEX.md:37` | IN PROGRESS | Correct — reflects open proof obligation |
| `gitbook/12-proof-and-invariant-map.md:204` | Uses `sorry`; tracked as TPI-D07 | Correct |
| `test_tier0_hygiene.sh` | Excludes `TPI-D*` tagged `sorry` markers | Correct — accepted technical debt, not hygiene violation |

**Conclusion:** The gap is narrow and precisely characterized — **not an algorithm absence, but proof infrastructure insufficiency for bounded-BFS soundness relative to graph reachability semantics.** The runtime behavior is correct and tested. Only the formal bridge between `serviceHasPathTo ... = false` and "no path exists in the graph" is missing.
