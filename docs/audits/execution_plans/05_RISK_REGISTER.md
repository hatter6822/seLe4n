# 05 — Risk Register

This document catalogs all identified risks, their mitigations, and decision points for TPI-D07 closure. Risks are ordered by priority.

---

## Risk 0 — Vacuous invariant definition (HIGHEST — RESOLVED)

**Status:** RESOLVED — Strategy B adopted. Invariant definition corrected.

**Risk:** Analysis during execution plan development revealed that `serviceDependencyAcyclic` as originally defined was **trivially unsatisfiable**. The BFS function `serviceHasPathTo st sid sid fuel` returns `true` immediately when `fuel ≥ 1` because the initial frontier `[sid]` contains the target `sid`, and the BFS checks `if node = target` before doing anything else.

Since `serviceBfsFuel st ≥ 256` always, `serviceHasPathTo st sid sid (serviceBfsFuel st) = true` for all `sid` and `st`. This made `serviceDependencyAcyclic st = ∀ sid, ¬ true = true`, which is `False`.

**Impact:** The hypothesis `hAcyc : serviceDependencyAcyclic st` was always contradictory, making the preservation theorem vacuously true.

**Resolution: Strategy B — Fix invariant + full proof**

The invariant definition has been corrected in `SeLe4n/Kernel/Service/Invariant.lean` to use declarative non-trivial-path acyclicity. Three new Layer 0 definitions were introduced:

```lean
-- D1: Direct dependency edge (one hop)
def serviceEdge (st : SystemState) (a b : ServiceId) : Prop :=
  ∃ svc, lookupService st a = some svc ∧ b ∈ svc.dependencies

-- D2: Reflexive-transitive closure of serviceEdge
inductive serviceReachable (st : SystemState) : ServiceId → ServiceId → Prop where
  | refl  : serviceReachable st a a
  | step  : serviceEdge st a b → serviceReachable st b c → serviceReachable st a c

-- D3: Non-trivial path (at least one step)
def serviceHasNontrivialPath (st : SystemState) (a b : ServiceId) : Prop :=
  ∃ mid, serviceEdge st a mid ∧ serviceReachable st mid b

-- Corrected acyclicity invariant (replaces vacuous BFS-based definition)
def serviceDependencyAcyclic (st : SystemState) : Prop :=
  ∀ sid, ¬ serviceHasNontrivialPath st sid sid
```

**Design rationale:** Option 3 (declarative from the start) was chosen over Options 1 and 2 because:
- It directly captures the intended semantic property (no non-trivial cycles).
- It avoids coupling the invariant statement to BFS implementation details.
- It simplifies the final proof by eliminating the need for BFS↔declarative equivalence theorems (EQ1/EQ2 from the original plan are subsumed).
- The BFS soundness bridge (Layer 2) still connects the operational cycle check to the declarative invariant.

**Superseded strategies:**

| Strategy | Approach | Trade-off | Status |
|---|---|---|---|
| **A: Trivial closure** | Replace `sorry` with `exfalso; exact hAcyc _`. | Closes TPI-D07 immediately but produces no security evidence. | Rejected |
| **B: Fix invariant + full proof** | Correct the invariant, build full proof infrastructure (M1–M3). | Produces genuine security evidence. | **Adopted** |
| **C: Conditional approach** | Close trivially, then fix later. | Pragmatic but defers real work. | Rejected |

---

## Risk 1 — Fuel adequacy proof (HIGH)

**Applicable only if Risk 0 Strategy B is chosen.**

**Risk:** `serviceBfsFuel st = st.objectIndex.length + 256` may not provably bound the number of distinct services in the graph. Service IDs are `Nat`-wrapped structs and the `services` field is a function `ServiceId → Option ServiceGraphEntry` — an infinite domain. The `objectIndex` tracks kernel objects, not services; a service's `backingObject` is in the object index, but `ServiceId` itself need not be.

**Impact:** Without fuel adequacy, the BFS soundness proof cannot guarantee the BFS explores all reachable nodes. The preservation theorem would require an additional precondition.

**Mitigations:**

| Strategy | Approach | Trade-off |
|---|---|---|
| **A: Model-level invariant** | Prove that registered services are bounded by a finite set derivable from state. Link service registration to object-index discipline. | Unconditional soundness. May require cross-subsystem invariant work. |
| **B: Preconditioned theorem** | Add explicit fuel-adequacy hypothesis. Document the assumption. | Pragmatic: closes cleanly. Assumption is dischargeable in concrete models. |
| **C: Strengthen BFS** | Modify `serviceHasPathTo` to use visited-set size as fuel. | Violates "no operational changes" constraint. Last resort. |

**Decision point:** Choose during M2 implementation.

---

## Risk 2 — List-based proof complexity (MEDIUM)

**Risk:** The dependency graph uses `List ServiceId` for `dependencies` and `List.filter`/`List.append` in the BFS. Lean 4 list lemmas can create rewriting-heavy proofs, especially for membership reasoning through `storeServiceState`.

**Impact:** Proofs may become long and fragile, requiring extensive `simp` lemma sets. If list reasoning becomes intractable, it could delay M1 and M2.

**Mitigations:**

1. **Introduce canonical membership lemmas early** (L1–L5 in M1) before attempting BFS invariant proofs in M2.
2. **Use `@[simp]` attributes** for edge-relation unfolding to reduce manual rewriting.
3. **Fallback: `Finset` abstraction.** If list reasoning becomes intractable, introduce a proof-only `Finset`-based layer over dependency lists. This adds definitions but simplifies membership proofs significantly.
4. **Audit available `List` lemmas** in the project's Lean version. Key lemmas needed:
   - `List.mem_append`
   - `List.mem_filter`
   - `List.mem_cons`
   - `List.mem_singleton`
   - `List.Nodup` properties (if needed for visited-set reasoning)

---

## Risk 3 — BFS loop invariant complexity (MEDIUM)

**Applicable only if Risk 0 Strategy B is chosen.**

**Risk:** The `go` function in `serviceHasPathTo` uses a non-standard recursion pattern where fuel is **recycled** on visited nodes (`go rest visited (fuel + 1)` passes the same fuel as input). This complicates induction arguments because the `Nat` argument doesn't strictly decrease in every recursive call.

**Impact:** The BFS loop invariant proof (B4) may require a more sophisticated induction strategy than simple `Nat` induction.

**Mitigations:**

1. **Lexicographic induction:** Use `(fuel, frontier.length)` as the induction measure. In the visited branch, fuel stays the same but frontier length decreases. In the expansion branch, fuel decreases.
2. **Strong induction on fuel** with `frontier.length` as a secondary measure for the same-fuel case.
3. **Auxiliary well-founded measure:** Define `measure := fuel * (frontier.length + 1) + frontier.length` or similar that strictly decreases on every recursive call.
4. **Alternative: prove BFS equivalence to a simpler function.** Show that `serviceHasPathTo` is equivalent to a "standard" BFS (with separate fuel for visited and expansion) and prove the invariant on the simpler version.

---

## Risk 4 — Documentation drift (LOW)

**Risk:** Four documentation files reference TPI-D07 status. If proof closure and doc updates land in separate PRs, interim states may be inconsistent.

**Mitigation:** Perform all documentation updates (M5) in the **same PR** as the proof closure (M3). The milestone ordering ensures M5 is the final step.

---

## Risk 5 — Lean version compatibility (LOW)

**Risk:** The proof tactics and `simp` lemma sets may depend on the specific Lean 4 version used by the project. A Lean toolchain update between milestones could break in-progress proofs.

**Mitigation:** Lock the Lean toolchain version during TPI-D07 work. Do not update `lean-toolchain` until the PR is merged.

---

## Decision log

| # | Decision | Status | Chosen option | Rationale |
|---|---|---|---|---|
| D1 | Invariant definition strategy (Risk 0) | **RESOLVED** | Strategy B (fix invariant + full proof) | BFS self-reachability confirmed vacuous. Declarative definition (Option 3) adopted for direct semantic clarity. Layer 0 definitions committed. |
| D2 | Fuel adequacy approach (Risk 1) | **PENDING** | — | Depends on D1 (now resolved). Strategy B confirmed: fuel adequacy needed for M2. |
| D3 | List reasoning strategy (Risk 2) | **PENDING** | — | Start with direct list lemmas; escalate to Finset if needed |
| D4 | BFS induction measure (Risk 3) | **PENDING** | — | Depends on D1 (now resolved). Strategy B confirmed: BFS induction needed for M2. |

---

## Risk interaction matrix

```
Risk 0 (vacuous invariant) — RESOLVED: Strategy B adopted
  │
  └── Strategy B (fix invariant) active:
        Risk 1 (fuel adequacy) → blocks M2
        Risk 2 (list complexity) → blocks M1, M2
        Risk 3 (BFS induction) → blocks M2
        Risk 4 (doc drift) → blocks M5
```
