# 05 — Risk Register

This document catalogs all identified risks, their mitigations, and decision points for TPI-D07 closure. Risks are ordered by priority.

---

## Risk 0 — Vacuous invariant definition (HIGHEST — newly identified)

**Risk:** Analysis during execution plan development revealed that `serviceDependencyAcyclic` as currently defined may be **trivially unsatisfiable**. The BFS function `serviceHasPathTo st sid sid fuel` returns `true` immediately when `fuel ≥ 1` because the initial frontier `[sid]` contains the target `sid`, and the BFS checks `if node = target` before doing anything else.

If `serviceBfsFuel st ≥ 1` (which it always is, since `objectIndex.length + 256 ≥ 256`), then `serviceHasPathTo st sid sid (serviceBfsFuel st) = true` for all `sid` and `st`. This means `serviceDependencyAcyclic st = ∀ sid, ¬ true = true`, which is `False`.

**Impact:** If confirmed, the hypothesis `hAcyc : serviceDependencyAcyclic st` is always contradictory, making the preservation theorem vacuously true. The `sorry` can be closed trivially.

**Verification steps:**

1. In a Lean 4 environment, evaluate `serviceHasPathTo (default : SystemState) ⟨0⟩ ⟨0⟩ 1` and check if it returns `true`.
2. Alternatively, prove `∀ st sid, serviceHasPathTo st sid sid 1 = true` by unfolding.
3. Check whether `#eval serviceHasPathTo ...` can be used in the codebase.

**Mitigations:**

| Strategy | Approach | Trade-off |
|---|---|---|
| **A: Trivial closure** | Replace `sorry` with `exfalso; exact hAcyc _` (or similar). Document the vacuous nature. | Closes TPI-D07 immediately but doesn't create meaningful proof infrastructure. |
| **B: Fix invariant + full proof** | Correct the invariant definition to exclude trivial self-reachability (see revised definition below), then build the full proof infrastructure (M1–M3). | Produces genuine security evidence but requires more work and changes a definition. |
| **C: Conditional approach** | Close the `sorry` trivially (Strategy A), then open a follow-up issue for invariant correction (Strategy B). | Pragmatic: unblocks the immediate obligation while tracking the deeper fix. |

**Revised invariant definition (if Strategy B is chosen):**

```lean
-- Option 1: Exclude self-loops in the BFS call
def serviceDependencyAcyclic (st : SystemState) : Prop :=
  ∀ sid₁ sid₂, sid₁ ≠ sid₂ →
    ¬ (serviceHasPathTo st sid₁ sid₂ (serviceBfsFuel st) = true ∧
       serviceHasPathTo st sid₂ sid₁ (serviceBfsFuel st) = true)

-- Option 2: Use non-trivial self-loop detection
-- The BFS would need to skip the immediate src=target check and look for
-- paths of length ≥ 1.

-- Option 3: Define acyclicity declaratively from the start
def serviceDependencyAcyclic (st : SystemState) : Prop :=
  ∀ sid, ¬ serviceHasNontrivialPath st sid sid
```

**Decision point:** Must be resolved at the start of M0. If Strategy A is chosen, M1 and M2 are unnecessary for TPI-D07 closure (but may still be valuable future infrastructure).

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
| D1 | Invariant definition strategy (Risk 0) | **RESOLVED** | Strategy B (fix invariant + declarative proof) | BFS self-reachability confirmed vacuous. Invariant redefined declaratively using `serviceNontrivialPath`. Layers 0-1, 3-4 proved; Layer 2 (BFS completeness) deferred as TPI-D07-BRIDGE with focused `sorry`. |
| D2 | Fuel adequacy approach (Risk 1) | **STRATEGY CHOSEN** | Strategy A first (explicit `serviceCountBounded` precondition), then Strategy B (model-level unconditional bound) as follow-up | M2 preparation analysis (§8 of `M2_BFS_SOUNDNESS.md`) recommends explicit bound hypothesis to decouple completeness proof from model analysis. The opaque `services : ServiceId → Option ServiceGraphEntry` function cannot be enumerated; Strategy A sidesteps this with a witness list. Strategy B requires proving a global invariant linking service registration to `objectIndex` membership. |
| D3 | List reasoning strategy (Risk 2) | **RESOLVED** | Direct list lemmas | `List.mem_append` and `List.mem_singleton` sufficed for edge characterization. No Finset escalation needed. Additional list lemmas identified for M2: `List.mem_filter` (critical for BFS expansion case), `List.mem_cons` (frontier reasoning). |
| D4 | BFS induction measure (Risk 3) | **STRATEGY CHOSEN** | Lexicographic `(fuel, frontier.length)` with strong induction | M2 preparation analysis (§5.3 of `M2_BFS_SOUNDNESS.md`) confirms that simple `Nat` induction on `fuel` fails due to fuel recycling in visited-skip branch. Lexicographic measure `(fuel, frontier.length)` matches the termination measure Lean used to accept the `go` definition: fuel same + frontier shorter in visited case; fuel decreasing in expansion case. |

---

## Risk interaction matrix

```
Risk 0 (vacuous invariant) — RESOLVED via Strategy B
  │
  └── Strategy B was chosen (fix invariant + declarative proof):
        Risk 1 (fuel adequacy) → Strategy A chosen (preconditioned)
        │   Phase 0-1 of M2 are independent of fuel adequacy
        │   Phase 2 integrates the bound
        Risk 2 (list complexity) → RESOLVED (direct lemmas suffice)
        │   Additional List.mem_filter needed for M2 expansion case
        Risk 3 (BFS induction) → Strategy chosen (lexicographic)
        │   (fuel, frontier.length) measure confirmed
        Risk 4 (doc drift) → mitigated by same-PR doc sync rule
```
