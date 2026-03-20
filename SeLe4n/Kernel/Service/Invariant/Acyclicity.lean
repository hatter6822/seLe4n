/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Service.Invariant.Policy

/-! # Service Dependency Acyclicity — seLe4n Extension

**This module is a seLe4n-specific extension with no analogue in real seL4.**

Provides machine-checked proofs that the service dependency graph remains
acyclic across all kernel operations. seL4 has no notion of service
dependencies — its capability derivation tree (CDT) tracks object lineage,
not service-level relationships. seLe4n's dependency graph is a separate
abstraction that enables reasoning about service startup ordering, cascade
failure boundaries, and isolation enforcement.

The proofs are layered:
- **Layer 0:** Declarative graph definitions (edges, reachability, acyclicity).
- **Layer 1:** Structural lemmas (transitivity, path lifting).
- **Layer 2:** Operation preservation (registration preserves acyclicity).
- **Layer 3:** Cross-subsystem composition with lifecycle and capability proofs.

See `Service/Operations.lean` for the full seLe4n extension rationale. -/

namespace SeLe4n.Kernel

open SeLe4n.Model


-- ============================================================================
-- Layer 0: Declarative graph definitions
-- ============================================================================

/-- Direct dependency edge: service `a` lists `b` as a dependency. -/
def serviceEdge (st : SystemState) (a b : ServiceId) : Prop :=
  ∃ svc, lookupService st a = some svc ∧ b ∈ svc.dependencies

/-- Reflexive-transitive closure of the service dependency edge relation. -/
inductive serviceReachable (st : SystemState) : ServiceId → ServiceId → Prop where
  | refl : serviceReachable st a a
  | step : serviceEdge st a b → serviceReachable st b c → serviceReachable st a c

/-- Non-trivial path in the service dependency graph (length ≥ 1).
    Declarative analogue of `serviceHasPathTo` for self-loop detection. -/
inductive serviceNontrivialPath (st : SystemState) : ServiceId → ServiceId → Prop where
  | single : serviceEdge st a b → serviceNontrivialPath st a b
  | cons   : serviceEdge st a b → serviceNontrivialPath st b c → serviceNontrivialPath st a c

/-- The service dependency graph is acyclic: no service has a dependency chain
leading back to itself.

Risk 0 fix (WS-D4/TPI-D07): The original BFS-based definition
`∀ sid, ¬ serviceHasPathTo st sid sid fuel = true` was vacuously unsatisfiable
because `serviceHasPathTo` returns `true` immediately when `src = target`.
This declarative definition correctly captures acyclicity as the absence
of non-trivial self-loops. -/
def serviceDependencyAcyclic (st : SystemState) : Prop :=
  ∀ sid, ¬ serviceNontrivialPath st sid sid

-- ============================================================================
-- Layer 1: Structural lemmas
-- ============================================================================

theorem serviceReachable_trans {st : SystemState} {a b c : ServiceId}
    (hab : serviceReachable st a b) (hbc : serviceReachable st b c) :
    serviceReachable st a c := by
  induction hab with
  | refl => exact hbc
  | step hedge _ ih => exact .step hedge (ih hbc)

theorem serviceReachable_of_edge {st : SystemState} {a b : ServiceId}
    (h : serviceEdge st a b) : serviceReachable st a b :=
  .step h .refl

theorem serviceReachable_of_nontrivialPath {st : SystemState} {a b : ServiceId}
    (h : serviceNontrivialPath st a b) : serviceReachable st a b := by
  induction h with
  | single hedge => exact serviceReachable_of_edge hedge
  | cons hedge _ ih => exact .step hedge ih

/-- Extend a single edge by a reachable suffix to form a nontrivial path.
    Proved by structural recursion on the `serviceReachable` argument. -/
theorem serviceNontrivialPath_of_edge_reachable {st : SystemState} {a b c : ServiceId}
    (hedge : serviceEdge st a b) (hreach : serviceReachable st b c) :
    serviceNontrivialPath st a c :=
  match hreach with
  | .refl => .single hedge
  | .step hedge2 htail =>
    .cons hedge (serviceNontrivialPath_of_edge_reachable hedge2 htail)

/-- A reachable pair with distinct endpoints has a nontrivial path. -/
theorem serviceNontrivialPath_of_reachable_ne {st : SystemState} {a b : ServiceId}
    (h : serviceReachable st a b) (hne : a ≠ b) : serviceNontrivialPath st a b := by
  cases h with
  | refl => exact absurd rfl hne
  | step hedge htail => exact serviceNontrivialPath_of_edge_reachable hedge htail

theorem serviceNontrivialPath_trans {st : SystemState} {a b c : ServiceId}
    (hab : serviceNontrivialPath st a b) (hbc : serviceNontrivialPath st b c) :
    serviceNontrivialPath st a c := by
  induction hab with
  | single hedge => exact .cons hedge hbc
  | cons hedge _ ih => exact .cons hedge (ih hbc)

theorem serviceNontrivialPath_step_right {st : SystemState} {a b c : ServiceId}
    (hab : serviceNontrivialPath st a b) (hbc : serviceEdge st b c) :
    serviceNontrivialPath st a c := by
  induction hab with
  | single hedge => exact .cons hedge (.single hbc)
  | cons hedge _ ih => exact .cons hedge (ih hbc)

-- ============================================================================
-- Layer 1: Frame lemmas for storeServiceState
-- ============================================================================

/-- Edge at a non-updated service is unchanged after storeServiceState. -/
theorem serviceEdge_storeServiceState_ne {st : SystemState} {svcId : ServiceId}
    {entry : ServiceGraphEntry} {a b : ServiceId} (ha : a ≠ svcId)
    (hSvcInv : st.services.invExt) :
    serviceEdge (storeServiceState svcId entry st) a b ↔ serviceEdge st a b := by
  constructor
  · rintro ⟨svc', hLookup, hMem⟩
    rw [storeServiceState_lookup_ne st svcId a entry ha hSvcInv] at hLookup
    exact ⟨svc', hLookup, hMem⟩
  · rintro ⟨svc', hLookup, hMem⟩
    rw [← storeServiceState_lookup_ne st svcId a entry ha hSvcInv] at hLookup
    exact ⟨svc', hLookup, hMem⟩

/-- Edge from the updated service reflects the new entry's dependencies. -/
theorem serviceEdge_storeServiceState_updated {st : SystemState} {svcId : ServiceId}
    {entry : ServiceGraphEntry} {b : ServiceId}
    (hSvcInv : st.services.invExt) :
    serviceEdge (storeServiceState svcId entry st) svcId b ↔ b ∈ entry.dependencies := by
  constructor
  · rintro ⟨svc', hLookup, hMem⟩
    rw [storeServiceState_lookup_eq st svcId entry hSvcInv] at hLookup
    cases hLookup
    exact hMem
  · intro hMem
    exact ⟨entry, storeServiceState_lookup_eq st svcId entry hSvcInv, hMem⟩

/-- Edge characterization after inserting depId into svcId's dependency list. -/
theorem serviceEdge_post_insert {st : SystemState} {svcId depId : ServiceId}
    {svc : ServiceGraphEntry} (hSvc : lookupService st svcId = some svc)
    {a b : ServiceId} (hSvcInv : st.services.invExt) :
    serviceEdge (storeServiceState svcId { svc with dependencies := svc.dependencies ++ [depId] } st) a b ↔
    ((a = svcId ∧ (b ∈ svc.dependencies ∨ b = depId)) ∨ (a ≠ svcId ∧ serviceEdge st a b)) := by
  by_cases ha : a = svcId
  · subst ha
    rw [serviceEdge_storeServiceState_updated hSvcInv]
    simp [List.mem_append]
  · rw [serviceEdge_storeServiceState_ne ha hSvcInv]
    constructor
    · intro h; exact Or.inr ⟨ha, h⟩
    · rintro (⟨hEq, _⟩ | ⟨_, h⟩)
      · exact absurd hEq ha
      · exact h

-- ============================================================================
-- Layer 2: Graph traversal completeness bridge (TPI-D07-BRIDGE)
-- ============================================================================

-- ---- M2A: Dependency-list helper and edge bridge ----

/-- Dependency list of a service node, defaulting to [] if unregistered. -/
private def lookupDeps (st : SystemState) (nd : ServiceId) : List ServiceId :=
  match lookupService st nd with | some svc => svc.dependencies | none => []

/-- serviceEdge ↔ membership in lookupDeps. -/
private theorem serviceEdge_iff_lookupDeps {st : SystemState} {a b : ServiceId} :
    serviceEdge st a b ↔ b ∈ lookupDeps st a := by
  unfold serviceEdge lookupDeps; constructor
  · rintro ⟨svc, hL, hM⟩; rw [hL]; exact hM
  · intro h
    cases hL : lookupService st a with
    | none => simp [hL] at h
    | some svc => simp only [hL] at h; exact ⟨svc, rfl, h⟩

-- ---- M2B: Graph traversal closure invariant (WS-G8: HashSet-based) ----

/-- Traversal closure: every visited node's successors are either visited or in the frontier.
WS-G8: Visited set is `Std.HashSet ServiceId` for O(1) membership. -/
private def bfsClosed (st : SystemState) (fr : List ServiceId) (vis : Std.HashSet ServiceId) : Prop :=
  ∀ v : ServiceId, vis.contains v = true → ∀ dep : ServiceId, serviceEdge st v dep → vis.contains dep = true ∨ dep ∈ fr

/-- CB2: Initial closure (empty visited set). -/
private theorem bfsClosed_init (st : SystemState) (fr : List ServiceId) :
    bfsClosed st fr {} := by
  intro v hv; rw [HashSet_contains_empty] at hv; exact absurd hv (by decide)

/-- CB3: Skip preserves closure. -/
private theorem bfsClosed_skip {st : SystemState} {nd : ServiceId}
    {rest : List ServiceId} {vis : Std.HashSet ServiceId}
    (hCl : bfsClosed st (nd :: rest) vis) (hVis : vis.contains nd = true) :
    bfsClosed st rest vis := by
  intro v hv dep he
  rcases hCl v hv dep he with h | h
  · exact Or.inl h
  · rcases List.mem_cons.mp h with heq | hr
    · subst heq; exact Or.inl hVis
    · exact Or.inr hr

/-- CB4: Expansion preserves closure.
WS-G8: Frontier is now DFS-ordered (deps ++ rest) and visited uses HashSet.insert. -/
private theorem bfsClosed_expand {st : SystemState} {nd : ServiceId}
    {rest : List ServiceId} {vis : Std.HashSet ServiceId}
    (hCl : bfsClosed st (nd :: rest) vis) (_hNV : vis.contains nd = false) :
    bfsClosed st ((lookupDeps st nd).filter (fun d => !(vis.contains d)) ++ rest) (vis.insert nd) := by
  intro v hv dep he
  rcases (HashSet_contains_insert_iff vis nd v).mp hv with rfl | hOV
  · -- v = nd: newly expanded node
    by_cases hDV : vis.contains dep = true
    · exact Or.inl ((HashSet_contains_insert_iff vis v dep).mpr (Or.inr hDV))
    · have hDVF : vis.contains dep = false := by
        cases h : vis.contains dep with
        | false => rfl
        | true => exact absurd h hDV
      exact Or.inr (List.mem_append.mpr (Or.inl
        (List.mem_filter.mpr ⟨serviceEdge_iff_lookupDeps.mp he, by simp [hDVF]⟩)))
  · -- v ∈ old visited: successors in old vis or old frontier
    rcases hCl v hOV dep he with h | h
    · exact Or.inl ((HashSet_contains_insert_iff vis nd dep).mpr (Or.inr h))
    · rcases List.mem_cons.mp h with heq | hr
      · subst heq; exact Or.inl (HashSet_contains_insert_self vis dep)
      · exact Or.inr (List.mem_append.mpr (Or.inr hr))

/-- CB1: Boundary lemma — if a visited node reaches the target (not visited),
    some frontier node also reaches the target.
WS-G8: Visited set is HashSet. -/
private theorem bfs_boundary_lemma {st : SystemState} {tgt : ServiceId}
    {fr : List ServiceId} {vis : Std.HashSet ServiceId} {v : ServiceId}
    (hR : serviceReachable st v tgt) :
    vis.contains v = true → vis.contains tgt = false → bfsClosed st fr vis →
    ∃ f ∈ fr, serviceReachable st f tgt := by
  induction hR with
  | refl =>
    intro hV hTNV _; rw [hV] at hTNV; exact absurd hTNV (by decide)
  | step he _hr ih =>
    intro hV hTNV hCl
    rcases hCl _ hV _ he with h | h
    · exact ih h hTNV hCl
    · exact ⟨_, h, _hr⟩

-- ---- Helpers: Universe, filter length, reachability ----

/-- A "traversal universe" is a Nodup node set that contains all registered
    services and is closed under dependencies. -/
private def bfsUniverse (st : SystemState) (ns : List ServiceId) : Prop :=
  ns.Nodup ∧
  (∀ sid, lookupService st sid ≠ none → sid ∈ ns) ∧
  (∀ sid ∈ ns, ∀ dep ∈ lookupDeps st sid, dep ∈ ns)

/-- Reachable nodes stay in the universe. -/
private theorem reach_in_universe {st : SystemState} {ns : List ServiceId}
    (hU : bfsUniverse st ns) {a b : ServiceId} (ha : a ∈ ns)
    (hR : serviceReachable st a b) : b ∈ ns := by
  induction hR with
  | refl => exact ha
  | step he _ ih => exact ih (hU.2.2 _ ha _ (serviceEdge_iff_lookupDeps.mp he))

/-- Monotone filter length: stricter predicate → shorter filtered list. -/
private theorem filter_mono {α : Type} (p1 p2 : α → Bool) (xs : List α)
    (h : ∀ x, p2 x = true → p1 x = true) :
    (xs.filter p2).length ≤ (xs.filter p1).length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.filter_cons]
    by_cases hp2 : p2 x = true
    · rw [if_pos hp2, if_pos (h x hp2)]; simp only [List.length_cons]; omega
    · rw [if_neg hp2]
      by_cases hp1 : p1 x = true
      · rw [if_pos hp1]; simp only [List.length_cons]; omega
      · rw [if_neg hp1]; exact ih

/-- Strict filter decrease: if some element passes p1 but not p2. -/
private theorem filter_strict {α : Type} [DecidableEq α]
    (p1 p2 : α → Bool) (xs : List α)
    (h_sub : ∀ x, p2 x = true → p1 x = true)
    (a : α) (ha : a ∈ xs) (hp1 : p1 a = true) (hp2 : p2 a = false)
    (hNod : xs.Nodup) :
    (xs.filter p2).length < (xs.filter p1).length := by
  induction xs with
  | nil => simp at ha
  | cons x rest ih =>
    have ⟨_, hNodR⟩ := List.nodup_cons.mp hNod
    simp only [List.filter_cons]
    rcases List.mem_cons.mp ha with heq | har
    · subst heq
      rw [if_pos hp1, if_neg (by simp [hp2])]
      simp only [List.length_cons]
      exact Nat.lt_succ_of_le (filter_mono p1 p2 rest h_sub)
    · have ih' := ih har hNodR
      by_cases hp2x : p2 x = true
      · rw [if_pos hp2x, if_pos (h_sub x hp2x)]; simp only [List.length_cons]; omega
      · rw [if_neg hp2x]
        by_cases hp1x : p1 x = true
        · rw [if_pos hp1x]; simp only [List.length_cons]; omega
        · rw [if_neg hp1x]; exact ih'

/-- Adding nd to visited strictly decreases the unvisited-universe count.
WS-G8: Updated for `Std.HashSet` visited set. -/
private theorem filter_vis_decrease (ns : List ServiceId) (nd : ServiceId)
    (vis : Std.HashSet ServiceId) (hMem : nd ∈ ns) (hNV : vis.contains nd = false) (hNod : ns.Nodup) :
    (ns.filter (fun x => !((vis.insert nd).contains x))).length <
    (ns.filter (fun x => !(vis.contains x))).length :=
  filter_strict (fun x => !(vis.contains x)) (fun x => !((vis.insert nd).contains x)) ns
    (by intro x hx
        simp only [Bool.not_eq_true'] at hx ⊢
        exact ((HashSet_not_contains_insert vis nd x).mp hx).2)
    nd hMem (by simp only [hNV]; decide)
    (by simp only [HashSet_contains_insert_self vis nd]; decide) hNod

/-- If a ≠ b and a reaches b, there exists an intermediate step. -/
private theorem step_of_reachable_ne {st : SystemState} {a b : ServiceId}
    (hR : serviceReachable st a b) (hne : a ≠ b) :
    ∃ mid, serviceEdge st a mid ∧ serviceReachable st mid b := by
  cases hR with
  | refl => exact absurd rfl hne
  | step hedge htail => exact ⟨_, hedge, htail⟩

-- ---- EQ lemmas: Equational unfolding of serviceHasPathTo.go ----
-- WS-G8: Updated for HashSet visited set and DFS frontier ordering.

private theorem go_tgt_eq {st : SystemState} {tgt : ServiceId}
    {rest : List ServiceId} {vis : Std.HashSet ServiceId} {f : Nat} :
    serviceHasPathTo.go st tgt (tgt :: rest) vis (f + 1) = true := by
  simp [serviceHasPathTo.go]

private theorem go_skip_eq {st : SystemState} {tgt nd : ServiceId}
    {rest : List ServiceId} {vis : Std.HashSet ServiceId} {f : Nat}
    (hNeq : nd ≠ tgt) (hVis : vis.contains nd = true) :
    serviceHasPathTo.go st tgt (nd :: rest) vis (f + 1) =
    serviceHasPathTo.go st tgt rest vis (f + 1) := by
  simp [serviceHasPathTo.go, hNeq, hVis]

private theorem go_expand_eq {st : SystemState} {tgt nd : ServiceId}
    {rest : List ServiceId} {vis : Std.HashSet ServiceId} {f : Nat}
    (hNeq : nd ≠ tgt) (hNV : vis.contains nd = false) :
    serviceHasPathTo.go st tgt (nd :: rest) vis (f + 1) =
    serviceHasPathTo.go st tgt
      ((lookupDeps st nd).filter (fun d => !(vis.contains d)) ++ rest)
      (vis.insert nd) f := by
  simp only [serviceHasPathTo.go, hNeq, ite_false, hNV]
  unfold lookupDeps; rfl

-- ---- CP1: Core graph traversal completeness ----
-- WS-G8: Updated for HashSet visited set and DFS frontier ordering.

set_option maxHeartbeats 800000 in
/-- Core completeness: if the frontier contains a node that can reach the target,
    and we have enough fuel, the traversal returns true.
WS-G8: Visited set is `Std.HashSet ServiceId`. Frontier is DFS-ordered. -/
private theorem go_complete
    (st : SystemState) (tgt : ServiceId)
    (fr : List ServiceId) (vis : Std.HashSet ServiceId) (fuel : Nat)
    (ns : List ServiceId)
    (hU : bfsUniverse st ns) (hTV : vis.contains tgt = false) (hCl : bfsClosed st fr vis)
    (hR : ∃ w ∈ fr, serviceReachable st w tgt)
    (hFB : ∀ x ∈ fr, x ∈ ns)
    (hFuel : (ns.filter (fun x => !(vis.contains x))).length ≤ fuel) :
    serviceHasPathTo.go st tgt fr vis fuel = true := by
  induction fuel using Nat.strongRecOn generalizing fr vis with
  | _ fuel ih_fuel =>
    induction fr generalizing vis with
    | nil => obtain ⟨w, hwM, _⟩ := hR; exact absurd hwM List.not_mem_nil
    | cons nd rest ih_fr =>
      obtain ⟨w, hwM, hwR⟩ := hR
      have htNs := reach_in_universe hU (hFB w hwM) hwR
      have htFilt : tgt ∈ ns.filter (fun x => !(vis.contains x)) := by
        rw [List.mem_filter]; exact ⟨htNs, by simp [hTV]⟩
      have hFP : 0 < (ns.filter (fun x => !(vis.contains x))).length := List.length_pos_of_mem htFilt
      obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
      by_cases hEq : nd = tgt
      · subst hEq; exact go_tgt_eq
      · by_cases hVis : vis.contains nd = true
        · -- Skip case
          rw [go_skip_eq hEq hVis]
          have hClR := bfsClosed_skip hCl hVis
          have hRR : ∃ f ∈ rest, serviceReachable st f tgt := by
            rcases List.mem_cons.mp hwM with heq | hw
            · subst heq; exact bfs_boundary_lemma hwR hVis hTV hClR
            · exact ⟨w, hw, hwR⟩
          exact ih_fr vis hTV hClR hRR
            (fun x hx => hFB x (List.mem_cons_of_mem nd hx)) hFuel
        · -- Expand case
          have hVisBool : vis.contains nd = false := by
            cases h : vis.contains nd with
            | false => rfl
            | true => exact absurd h hVis
          rw [go_expand_eq hEq hVisBool]
          have hNdNs := hFB nd List.mem_cons_self
          have hFuelDec := filter_vis_decrease ns nd vis hNdNs hVisBool hU.1
          apply ih_fuel fuel' (by omega)
          · -- tgt ∉ vis.insert nd
            rw [Std.HashSet.contains_insert]
            simp only [Bool.or_eq_false_iff]
            exact ⟨by cases h : (nd == tgt) <;> simp_all, hTV⟩
          · exact bfsClosed_expand hCl hVisBool
          · rcases List.mem_cons.mp hwM with heq | hw
            · rw [heq] at hwR
              obtain ⟨mid, hedge, htail⟩ := step_of_reachable_ne hwR hEq
              have hMidDeps : mid ∈ lookupDeps st nd :=
                serviceEdge_iff_lookupDeps.mp hedge
              by_cases hMidVis : vis.contains mid = true
              · have hClE := bfsClosed_expand hCl hVisBool
                have hMidNewVis : (vis.insert nd).contains mid = true :=
                  (HashSet_contains_insert_iff vis nd mid).mpr (Or.inr hMidVis)
                have hTgtNewVis : (vis.insert nd).contains tgt = false := by
                  rw [Std.HashSet.contains_insert]
                  simp only [Bool.or_eq_false_iff]
                  exact ⟨by cases h : (nd == tgt) <;> simp_all, hTV⟩
                exact bfs_boundary_lemma htail hMidNewVis hTgtNewVis hClE
              · have hMidVisBool : vis.contains mid = false := by
                  cases h : vis.contains mid with
                  | false => rfl
                  | true => exact absurd h hMidVis
                exact ⟨mid,
                  List.mem_append.mpr (Or.inl
                    (List.mem_filter.mpr ⟨hMidDeps, by simp [hMidVisBool]⟩)),
                  htail⟩
            · exact ⟨w, List.mem_append.mpr (Or.inr hw), hwR⟩
          · intro x hx
            rcases List.mem_append.mp hx with hxd | hxr
            · exact hU.2.2 nd hNdNs x (List.mem_filter.mp hxd).1
            · exact hFB x (List.mem_cons_of_mem nd hxr)
          · omega

/-- State-level bound: a traversal universe exists within the fuel budget.
    This is a precondition for the completeness bridge. -/
def serviceCountBounded (st : SystemState) : Prop :=
  ∃ ns : List ServiceId,
    bfsUniverse st ns ∧ ns.length ≤ serviceBfsFuel st

/-- The source of a nontrivial path is a registered service. -/
private theorem registered_of_nontrivialPath_src {st : SystemState} {a b : ServiceId}
    (h : serviceNontrivialPath st a b) : lookupService st a ≠ none := by
  cases h with
  | single hedge => obtain ⟨svc, hL, _⟩ := hedge; simp [hL]
  | cons hedge _ => obtain ⟨svc, hL, _⟩ := hedge; simp [hL]

/-- Graph traversal completeness bridge: a nontrivial path between distinct services
is detected by `serviceHasPathTo` with `serviceBfsFuel` fuel.

This connects the declarative path relation to the executable graph traversal check
used in `serviceRegisterDependency`. Completeness is established by a formal
loop-invariant argument (M2/TPI-D07-BRIDGE): the traversal maintains a closure
invariant on the visited set, and a decreasing measure on the unvisited universe
nodes ensures termination with the correct result.

WS-G8: Visited set is `Std.HashSet ServiceId` (O(1) membership). Traversal
order is DFS (prepend) instead of BFS (append). Cycle detection correctness is
order-independent.

The `serviceCountBounded` hypothesis ensures that the set of reachable service
nodes fits within the fuel budget. -/
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (hPath : serviceNontrivialPath st a b)
    (hNe : a ≠ b)
    (hBound : serviceCountBounded st) :
    serviceHasPathTo st a b (serviceBfsFuel st) = true := by
  obtain ⟨ns, hU, hLen⟩ := hBound
  have haSrc := registered_of_nontrivialPath_src hPath
  have haInNs := hU.2.1 a haSrc
  apply go_complete st b [a] {} (serviceBfsFuel st) ns hU
  · exact HashSet_contains_empty
  · exact bfsClosed_init st [a]
  · exact ⟨a, List.mem_cons_self, serviceReachable_of_nontrivialPath hPath⟩
  · intro x hx; rcases List.mem_cons.mp hx with heq | h
    · subst heq; exact haInNs
    · exact absurd h List.not_mem_nil
  · -- fuel: ns.filter (fun x => !(({} : HashSet).contains x)).length ≤ serviceBfsFuel st
    -- Since empty.contains is always false, filter keeps all elements
    have hFiltId : ns.filter (fun x => !(({} : Std.HashSet ServiceId).contains x)) = ns := by
      rw [List.filter_eq_self]
      intro x _
      simp only [HashSet_contains_empty, Bool.not_false]
    rw [hFiltId]; exact hLen

-- ============================================================================
-- Layer 3: Post-insertion nontrivial path decomposition
-- ============================================================================

/-- Any nontrivial path in the post-insertion state either:
(1) consists entirely of pre-state edges, or
(2) uses the new svcId → depId edge, yielding pre-state reachability
    from the source to svcId and from depId to the target. -/
theorem nontrivialPath_post_insert_cases
    {st : SystemState} {svcId depId : ServiceId}
    {svc : ServiceGraphEntry} (hSvc : lookupService st svcId = some svc)
    {a b : ServiceId}
    (hSvcInv : st.services.invExt)
    (hPath : serviceNontrivialPath
      (storeServiceState svcId { svc with dependencies := svc.dependencies ++ [depId] } st) a b) :
    serviceNontrivialPath st a b ∨
    (serviceReachable st a svcId ∧ serviceReachable st depId b) := by
  induction hPath with
  | single hedge =>
    rcases (serviceEdge_post_insert hSvc hSvcInv).mp hedge with ⟨rfl, hOr⟩ | ⟨hNe, hOld⟩
    · rcases hOr with hOld | rfl
      · -- Old edge from svcId
        exact Or.inl (.single ⟨svc, hSvc, hOld⟩)
      · -- New edge: svcId → depId
        exact Or.inr ⟨.refl, .refl⟩
    · exact Or.inl (.single hOld)
  | cons hedge _ ih =>
    rcases (serviceEdge_post_insert hSvc hSvcInv).mp hedge with ⟨rfl, hOr⟩ | ⟨hNe, hOld⟩
    · rcases hOr with hOld | rfl
      · -- Old edge from svcId → mid, then path mid →+ b
        rcases ih with hPre | ⟨hReach1, hReach2⟩
        · exact Or.inl (.cons ⟨svc, hSvc, hOld⟩ hPre)
        · exact Or.inr ⟨.refl, hReach2⟩
      · -- New edge: svcId → depId, then path depId →+ b
        rcases ih with hPre | ⟨_, hReach2⟩
        · exact Or.inr ⟨.refl, serviceReachable_of_nontrivialPath hPre⟩
        · exact Or.inr ⟨.refl, hReach2⟩
    · -- Old edge from a → mid (a ≠ svcId), then path mid →+ b
      rcases ih with hPre | ⟨hReach1, hReach2⟩
      · exact Or.inl (.cons hOld hPre)
      · exact Or.inr ⟨.step hOld hReach1, hReach2⟩

-- ============================================================================
-- Layer 4: Acyclicity preservation (TPI-D07 closure)
-- ============================================================================

/-- After a successful dependency registration, the dependency graph remains acyclic.

The `serviceRegisterDependency` function checks whether `depId` can reach
`svcId` through existing edges before adding `svcId → depId`. If the check
finds a path, it returns `cyclicDependency`. On success, no path existed,
so adding the edge preserves acyclicity.

Risk 0 resolution (WS-D4/TPI-D07): The vacuous BFS-based invariant has been
replaced with a declarative acyclicity definition. The preservation proof is
genuine — it proceeds by post-insertion path decomposition and derives a
contradiction from the BFS cycle-detection check. BFS completeness
(`bfs_complete_for_nontrivialPath`) is now formally proved (M2/TPI-D07-BRIDGE),
contingent on `serviceCountBounded`, which asserts that the set of reachable
service nodes fits within the BFS fuel budget. -/
theorem serviceRegisterDependency_preserves_acyclicity
    (svcId depId : ServiceId) (st st' : SystemState)
    (hReg : serviceRegisterDependency svcId depId st = .ok ((), st'))
    (hAcyc : serviceDependencyAcyclic st)
    (hBound : serviceCountBounded st)
    (hSvcInv : st.services.invExt) :
    serviceDependencyAcyclic st' := by
  unfold serviceRegisterDependency at hReg
  cases hSvc : lookupService st svcId with
  | none => simp [hSvc] at hReg
  | some svc =>
    simp only [hSvc] at hReg
    cases hDep : lookupService st depId with
    | none => simp [hDep] at hReg
    | some depSvc =>
      simp only [hDep] at hReg
      by_cases hSelf : svcId = depId
      · simp [hSelf] at hReg
      · simp only [hSelf, ite_false] at hReg
        by_cases hExists : depId ∈ svc.dependencies
        · -- Idempotent: st' = st
          simp [hExists] at hReg
          cases hReg
          exact hAcyc
        · simp only [hExists, ite_false] at hReg
          by_cases hCycle : serviceHasPathTo st depId svcId (serviceBfsFuel st) = true
          · simp [hCycle] at hReg
          · simp only [hCycle] at hReg
            unfold storeServiceEntry at hReg
            simp at hReg
            cases hReg
            -- Goal: serviceDependencyAcyclic (storeServiceState svcId {svc with ...} st)
            -- Strategy: suppose a post-state cycle, decompose, derive contradiction
            intro sid hCycleSid
            rcases nontrivialPath_post_insert_cases hSvc hSvcInv hCycleSid with hPre | ⟨hReach1, hReach2⟩
            · -- Case 1: cycle uses only old edges → pre-state cycle
              exact hAcyc sid hPre
            · -- Case 2: cycle uses new edge → pre-state path depId →* svcId
              -- Compose: depId →* sid →* svcId via serviceReachable_trans
              have hDepSvc : serviceReachable st depId svcId :=
                serviceReachable_trans hReach2 hReach1
              -- Since svcId ≠ depId, this reachability is nontrivial
              have hNontrivial : serviceNontrivialPath st depId svcId :=
                serviceNontrivialPath_of_reachable_ne hDepSvc (Ne.symm hSelf)
              -- BFS completeness: nontrivial path + bounded universe → BFS returns true
              have hBfsTrue : serviceHasPathTo st depId svcId (serviceBfsFuel st) = true :=
                bfs_complete_for_nontrivialPath hNontrivial (Ne.symm hSelf) hBound
              -- Contradiction with the BFS check that returned false
              exact absurd hBfsTrue hCycle

-- ============================================================================
-- H-08/WS-E3: Graph traversal soundness in Service/Invariant context
-- ============================================================================

/-- H-08/WS-E3: Traversal conservatively reports a path when fuel is exhausted.
Under the zero-fuel base case the traversal returns `true`, preventing any
dependency registration when the fuel budget is insufficient. -/
theorem serviceHasPathTo_fuel_zero (st : SystemState) (src target : ServiceId) :
    serviceHasPathTo st src target 0 = true := by
  simp [serviceHasPathTo, serviceHasPathTo.go]

/-- H-08/WS-E3 adequacy: when the traversal returns `false`, there genuinely is
no nontrivial path from `a` to `b`. This is the soundness direction —
the contrapositive of `bfs_complete_for_nontrivialPath`. -/
theorem bfs_false_implies_no_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (hBfs : serviceHasPathTo st a b (serviceBfsFuel st) = false)
    (hNe : a ≠ b)
    (hBound : serviceCountBounded st) :
    ¬ serviceNontrivialPath st a b := by
  intro hPath
  have hTrue := bfs_complete_for_nontrivialPath hPath hNe hBound
  rw [hTrue] at hBfs
  cases hBfs

-- ============================================================================
-- WS-H13: Graph transfer through identity-preserving storeServiceState
-- ============================================================================

/-- When the stored entry has the same dependencies as the original service,
all edges are preserved. -/
private theorem serviceEdge_of_storeServiceState_sameDeps
    {st : SystemState} {svcId : ServiceId} {svc : ServiceGraphEntry}
    (hSvc : lookupService st svcId = some svc)
    {entry : ServiceGraphEntry} (hDeps : entry.dependencies = svc.dependencies)
    (hSvcInv : st.services.invExt)
    {a b : ServiceId} :
    serviceEdge (storeServiceState svcId entry st) a b ↔ serviceEdge st a b := by
  by_cases ha : a = svcId
  · subst ha
    rw [serviceEdge_storeServiceState_updated hSvcInv]
    constructor
    · intro h; exact ⟨svc, hSvc, hDeps ▸ h⟩
    · rintro ⟨svc', hL, hM⟩; rw [hSvc] at hL; cases hL; rw [hDeps]; exact hM
  · exact serviceEdge_storeServiceState_ne ha hSvcInv

/-- Nontrivial paths are preserved through same-deps store. -/
private theorem serviceNontrivialPath_of_storeServiceState_sameDeps
    {st : SystemState} {svcId : ServiceId} {svc : ServiceGraphEntry}
    (hSvc : lookupService st svcId = some svc)
    {entry : ServiceGraphEntry} (hDeps : entry.dependencies = svc.dependencies)
    (hSvcInv : st.services.invExt)
    {a b : ServiceId} :
    serviceNontrivialPath (storeServiceState svcId entry st) a b ↔
    serviceNontrivialPath st a b := by
  constructor
  · intro h; induction h with
    | single he => exact .single ((serviceEdge_of_storeServiceState_sameDeps hSvc hDeps hSvcInv).mp he)
    | cons he _ ih => exact .cons ((serviceEdge_of_storeServiceState_sameDeps hSvc hDeps hSvcInv).mp he) ih
  · intro h; induction h with
    | single he => exact .single ((serviceEdge_of_storeServiceState_sameDeps hSvc hDeps hSvcInv).mpr he)
    | cons he _ ih => exact .cons ((serviceEdge_of_storeServiceState_sameDeps hSvc hDeps hSvcInv).mpr he) ih

/-- Acyclicity is preserved through same-deps store. -/
private theorem serviceDependencyAcyclic_of_storeServiceState_sameDeps
    {st : SystemState} {svcId : ServiceId} {svc : ServiceGraphEntry}
    (hSvc : lookupService st svcId = some svc)
    {entry : ServiceGraphEntry} (hDeps : entry.dependencies = svc.dependencies)
    (hSvcInv : st.services.invExt)
    (hAcyc : serviceDependencyAcyclic st) :
    serviceDependencyAcyclic (storeServiceState svcId entry st) := by
  intro sid hPath
  exact hAcyc sid ((serviceNontrivialPath_of_storeServiceState_sameDeps hSvc hDeps hSvcInv).mp hPath)

-- ============================================================================
-- WS-H13/M-17: serviceCountBounded invariant integration
-- ============================================================================

/-- WS-H13/M-17: Service graph invariant bundle — combines service dependency
acyclicity with the service count bound. The count bound is required by
`bfs_complete_for_nontrivialPath` (BFS/DFS completeness), which in turn is
required by `serviceRegisterDependency_preserves_acyclicity`.

By maintaining both as a bundle, the acyclicity preservation proof chain is
self-contained: the count bound hypothesis is always available when needed. -/
def serviceGraphInvariant (st : SystemState) : Prop :=
  serviceDependencyAcyclic st ∧ serviceCountBounded st

/-- bfsUniverse is preserved through same-deps storeServiceState
    (objectIndex unchanged). -/
private theorem bfsUniverse_of_storeServiceState_sameDeps
    {st : SystemState} {svcId : ServiceId} {svc : ServiceGraphEntry}
    (hSvc : lookupService st svcId = some svc)
    {entry : ServiceGraphEntry} (hDeps : entry.dependencies = svc.dependencies)
    (hSvcInv : st.services.invExt)
    {ns : List ServiceId} (hU : bfsUniverse st ns) :
    bfsUniverse (storeServiceState svcId entry st) ns := by
  refine ⟨hU.1, ?_, ?_⟩
  · intro sid' hLookup'
    by_cases hEq : sid' = svcId
    · exact hU.2.1 sid' (by rw [hEq, hSvc]; exact Option.some_ne_none _)
    · rw [storeServiceState_lookup_ne st svcId sid' entry hEq hSvcInv] at hLookup'
      exact hU.2.1 sid' hLookup'
  · intro sid' hMem dep hDepIn
    unfold lookupDeps at hDepIn
    by_cases hEq : sid' = svcId
    · rw [hEq, storeServiceState_lookup_eq st svcId entry hSvcInv] at hDepIn
      simp at hDepIn; rw [hDeps] at hDepIn
      exact hU.2.2 sid' hMem dep
        (by unfold lookupDeps; rw [hEq, hSvc]; exact hDepIn)
    · rw [storeServiceState_lookup_ne st svcId sid' entry hEq hSvcInv] at hDepIn
      exact hU.2.2 sid' hMem dep (by unfold lookupDeps; exact hDepIn)

/-- serviceCountBounded is preserved through same-deps storeServiceState. -/
private theorem serviceCountBounded_of_storeServiceState_sameDeps
    {st : SystemState} {svcId : ServiceId} {svc : ServiceGraphEntry}
    (hSvc : lookupService st svcId = some svc)
    {entry : ServiceGraphEntry} (hDeps : entry.dependencies = svc.dependencies)
    (hSvcInv : st.services.invExt)
    (hBound : serviceCountBounded st) :
    serviceCountBounded (storeServiceState svcId entry st) := by
  obtain ⟨ns, hU, hLen⟩ := hBound
  refine ⟨ns, bfsUniverse_of_storeServiceState_sameDeps hSvc hDeps hSvcInv hU, ?_⟩
  simp [serviceBfsFuel, storeServiceState]; exact hLen

/-- serviceGraphInvariant is preserved through same-deps storeServiceState. -/
private theorem serviceGraphInvariant_of_storeServiceState_sameDeps
    {st : SystemState} {svcId : ServiceId} {svc : ServiceGraphEntry}
    (hSvc : lookupService st svcId = some svc)
    {entry : ServiceGraphEntry} (hDeps : entry.dependencies = svc.dependencies)
    (hSvcInv : st.services.invExt)
    (hInv : serviceGraphInvariant st) :
    serviceGraphInvariant (storeServiceState svcId entry st) := by
  exact ⟨serviceDependencyAcyclic_of_storeServiceState_sameDeps hSvc hDeps hSvcInv hInv.1,
         serviceCountBounded_of_storeServiceState_sameDeps hSvc hDeps hSvcInv hInv.2⟩

/-- WS-H13: `serviceRegisterDependency` preserves the service graph invariant.
This closes the gap where `serviceCountBounded` was required as a hypothesis
but never proved as a maintained invariant. -/
theorem serviceRegisterDependency_preserves_serviceGraphInvariant
    (svcId depId : ServiceId) (st st' : SystemState)
    (hReg : serviceRegisterDependency svcId depId st = .ok ((), st'))
    (hInv : serviceGraphInvariant st)
    (hSvcInv : st.services.invExt) :
    serviceGraphInvariant st' := by
  obtain ⟨hAcyc, hBound⟩ := hInv
  constructor
  · exact serviceRegisterDependency_preserves_acyclicity svcId depId st st' hReg hAcyc hBound hSvcInv
  · -- serviceCountBounded transfers: storeServiceState only changes services,
    -- not objectIndex, so serviceBfsFuel is preserved. The universe list
    -- is extended at most by one node (the updated service entry).
    unfold serviceRegisterDependency at hReg
    cases hSvc : lookupService st svcId with
    | none => simp [hSvc] at hReg
    | some svc =>
        simp only [hSvc] at hReg
        cases hDep : lookupService st depId with
        | none => simp [hDep] at hReg
        | some _ =>
            simp only [hDep] at hReg
            by_cases hSelf : svcId = depId
            · simp [hSelf] at hReg
            · simp only [hSelf] at hReg
              by_cases hExists : depId ∈ svc.dependencies
              · simp [hExists] at hReg; cases hReg; exact hBound
              · simp only [hExists] at hReg
                by_cases hCycle : serviceHasPathTo st depId svcId (serviceBfsFuel st)
                · simp [hCycle] at hReg
                · simp only [hCycle] at hReg
                  unfold storeServiceEntry at hReg; simp at hReg; cases hReg
                  -- Post-state: storeServiceState preserves objectIndex and services
                  -- are a superset, so the existing universe still works.
                  obtain ⟨ns, hU, hLen⟩ := hBound
                  refine ⟨ns, ⟨hU.1, ?_, ?_⟩, ?_⟩
                  · -- All registered services in post-state are in ns
                    intro sid' hLookup'
                    by_cases hEq : sid' = svcId
                    · exact hU.2.1 sid' (by
                        rw [hEq, hSvc]; exact Option.some_ne_none _)
                    · rw [storeServiceState_lookup_ne st svcId sid' _ hEq hSvcInv] at hLookup'
                      exact hU.2.1 sid' hLookup'
                  · -- Dependency closure: new dep list for svcId includes depId
                    intro sid' hMem dep hDepMem
                    unfold lookupDeps at hDepMem
                    by_cases hEq : sid' = svcId
                    · rw [hEq, storeServiceState_lookup_eq st svcId _ hSvcInv] at hDepMem
                      simp at hDepMem
                      cases hDepMem with
                      | inl h =>
                          exact hU.2.2 sid' hMem dep
                            (by unfold lookupDeps; rw [hEq, hSvc]; exact h)
                      | inr h =>
                          exact hU.2.1 dep (by rw [h, hDep]; exact Option.some_ne_none _)
                    · rw [storeServiceState_lookup_ne st svcId sid' _ hEq hSvcInv] at hDepMem
                      exact hU.2.2 sid' hMem dep (by unfold lookupDeps; exact hDepMem)
                  · -- Fuel preserved: objectIndex unchanged
                    simp [storeServiceState, serviceBfsFuel] at hLen ⊢; exact hLen

-- ============================================================================
-- WS-F6/D4: Default state satisfaction
-- ============================================================================

/-- WS-F6/D4a: Default state has empty services, so `serviceCountBounded` holds
with `ns := []`. The empty list is trivially a `bfsUniverse` (no services to
include), and `[].length = 0 ≤ serviceBfsFuel default`. -/
private theorem default_lookupService_none (sid : ServiceId) :
    lookupService default sid = none := by
  unfold lookupService
  exact RHTable_get?_empty 16 (by omega)

theorem default_serviceCountBounded : serviceCountBounded default := by
  refine ⟨[], ⟨List.nodup_nil, ?_, ?_⟩, ?_⟩
  · intro sid hLookup
    exact absurd (default_lookupService_none sid) hLookup
  · intro sid hMem
    contradiction
  · simp [serviceBfsFuel]

/-- WS-F6/D4: Default state satisfies the full service graph invariant. -/
theorem default_serviceGraphInvariant : serviceGraphInvariant default := by
  refine ⟨?_, default_serviceCountBounded⟩
  intro a hPath
  cases hPath with
  | single h =>
      obtain ⟨svc, hL, _⟩ := h
      have := default_lookupService_none a; rw [this] at hL; nomatch hL
  | cons h _ =>
      obtain ⟨svc, hL, _⟩ := h
      have := default_lookupService_none a; rw [this] at hL; nomatch hL

end SeLe4n.Kernel
