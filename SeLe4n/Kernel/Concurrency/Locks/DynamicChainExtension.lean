-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Kernel.Scheduler.PriorityInheritance.BlockingGraph
import SeLe4n.Kernel.Concurrency.Locks.Kind
import SeLe4n.Kernel.Concurrency.Locks.LockSet
import SeLe4n.Kernel.Concurrency.Locks.LockIdProjection
import SeLe4n.Kernel.Concurrency.Locks.LockSetTransitions
import SeLe4n.Kernel.Concurrency.Locks.WithLockSet
import SeLe4n.Kernel.Concurrency.Locks.LockSetHeld
import SeLe4n.Kernel.Concurrency.Locks.LockSet2PL

/-!
# WS-SM SM3.C.11 — Dynamic priority-inheritance chain-walk locking

The three PIP-invoking user syscalls (`.call`, `.reply`,
`.replyRecv`) trigger a Priority Inheritance Protocol (PIP) chain
walk via `propagatePriorityInheritance` or
`revertPriorityInheritance`.  The chain's length is
**state-discovered** — it depends on the current blocking-graph
topology (`blockingServer` relation), not on syscall arguments.

A purely static `lockSet` cannot enumerate the chain TCBs in
advance, so SM3.C.11 introduces a *dynamic* extension to the
2PL discipline that preserves deadlock-freedom under the SM0.I
total order on `LockId`.

## Three structural signals from SM3.B

SM3.B.3 (audit-pass-5) exposes the chain start point at the type
level via three signals:

* `pipChainStart_endpointCall : ... → Option ThreadId`
* `pipChainStart_endpointReply : ... → Option ThreadId`
* `pipChainStart_replyRecv : ... → Option ThreadId`

When non-`none`, the kernel transition will walk the chain
beginning at the returned `ThreadId` after the core action
completes.  SM3.C.11 wires the dynamic extension that consumes
these signals.

## Acquisition strategy: optimistic walk + verify

The recommended strategy (per plan §5.3 SM3.C.11.a):

1. Acquire the static `lockSet_<τ> args` (which includes
   `startTid` itself).
2. Read the next chain link (`blockingServer st startTid`) under
   `startTid`'s write lock.
3. Release `startTid`'s write lock.
4. CAS-acquire the next TCB's write lock in `ObjId.val`
   ascending order (preserving the SM0.I total order on
   `.tcb`-level locks).
5. Re-verify the chain link from the new TCB's vantage point.
   On mismatch (the graph moved between steps 2 and 4), release
   and retry from `startTid` (bounded by `MAX_PIP_RETRIES = 64`).
6. Repeat steps 2-5 until `blockingServer` returns `none` (end
   of chain).

The bounded retry budget guarantees termination: even under
pathological contention, the walker either completes the chain
within 64 retries OR panics (preferable to a silent infinite
loop in the host event handler).

## Deadlock-freedom for dynamic chains

The strategy preserves deadlock-freedom (Theorem 3.7.1) because:

* Each chain step acquires a TCB lock at strictly higher
  `ObjId.val` than the previously-released one.
* Two cores walking different chains can interleave their
  acquires safely: each only holds AT MOST TWO TCB locks at any
  instant (the current chain step + the candidate next step
  during the CAS).
* Any cycle would require one core to acquire LOWER `ObjId.val`s
  while another acquires HIGHER — impossible under the strict
  ascending discipline.

## Used by

SM3.C.11.b — the per-transition `withLockSet` wrappers for the
3 PIP-invoking transitions consume `pipChainStart_<τ>` after the
static lock-set is held and `action` completes.
-/

namespace SeLe4n.Kernel.Concurrency

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.PriorityInheritance

-- ============================================================================
-- §1 — Constants
-- ============================================================================

/-- WS-SM SM3.C.11.e: chain-traversal fuel bound for the abstract
dynamic chain walker.

**Audit-pass-1 (Comments 2 & 6) — fuel semantics clarified.**  The
codex review correctly observed that at the abstract layer this
value is consumed *per chain step* (each `.extended` step decrements
it), so it functions as a **maximum chain-traversal depth**, not as
a per-step retry budget.  The two notions are distinct and live at
different layers:

* **Abstract layer (this module)**: the walker is a *pure function*
  over a *fixed* `SystemState`.  There is nothing to "retry" — re-
  running `walkStep` on the same state yields the same result.  The
  fuel is therefore purely a **structural termination bound** that
  caps the chain depth the walker will traverse, guaranteeing the
  recursion terminates (Lean accepts the `fuel`-decreasing
  definition).  `walkAndAcquireAux_terminated_length_le` proves the
  produced path length is `≤ initial + fuel`.

* **FFI / runtime layer (SM5+, deferred)**: the optimistic-walk +
  verify strategy uses a *separate* per-step retry budget to handle
  concurrent graph mutation (re-read `blockingServer`, release,
  re-acquire).  That budget is the "retry" notion the plan §5.3
  describes; it is NOT this constant.

The value 64 is well above any realistic blocking-chain depth
(under SM3.D's `blockingAcyclic` invariant the chain length is
bounded by the number of TCBs, and real reply-blocking chains are
only a few levels deep).  A chain deeper than 64 returns
`.exhausted` rather than looping; on hardware the runtime layer
treats exhaustion as a panic (preferable to a silent infinite loop
in the IPC host-event handler), pre-empted in practice by SM3.D.4's
deadlock-freedom guarantee. -/
def MAX_PIP_RETRIES : Nat := 64

/-- WS-SM SM3.C.11.e: `MAX_PIP_RETRIES` is positive. -/
theorem MAX_PIP_RETRIES_pos : 0 < MAX_PIP_RETRIES := by decide

-- ============================================================================
-- §2 — Chain-walk path representation (SM3.C.11.a)
-- ============================================================================

/-- WS-SM SM3.C.11: a PIP chain walk's *path* — the ordered list
of `ThreadId`s currently held by the walker, in acquisition order
(by `ObjId.val` ascending).

The first element is always the `startTid` argument of the
walker; subsequent elements are derived from `blockingServer`
chain traversal. -/
structure PipChainPath where
  /-- The chain start, always the first element of `path`. -/
  startTid : ThreadId
  /-- The ordered list of TCBs traversed.  Invariant: `.head? =
      some startTid` (the structure guarantees this via the
      `wf` field). -/
  path : List ThreadId
  /-- Well-formedness: the path begins at `startTid`. -/
  wf_head : path.head? = some startTid
  deriving Repr

namespace PipChainPath

/-- WS-SM SM3.C.11: construct a singleton path containing only
the start TCB.  This is the base case of the walker. -/
def singleton (tid : ThreadId) : PipChainPath :=
  { startTid := tid,
    path := [tid],
    wf_head := rfl }

@[simp] theorem singleton_startTid (tid : ThreadId) :
    (singleton tid).startTid = tid := rfl

@[simp] theorem singleton_path (tid : ThreadId) :
    (singleton tid).path = [tid] := rfl

/-- WS-SM SM3.C.11: length of a path. -/
def length (p : PipChainPath) : Nat := p.path.length

@[simp] theorem singleton_length (tid : ThreadId) :
    (singleton tid).length = 1 := rfl

end PipChainPath

-- ============================================================================
-- §3 — Dynamic chain walk (SM3.C.11.a)
-- ============================================================================

/-- WS-SM SM3.C.11.a: outcome of a single bounded chain-walk step.

* `.extended path` — the walker successfully extended the path by
  one step.  The new path is `path` (which contains the previous
  path plus the next-chain TCB).
* `.terminated path` — the walker reached the end of the chain
  (`blockingServer` returned `none` at the tail).  The path is
  complete.
* `.exhausted` — the walker exceeded `MAX_PIP_RETRIES` without
  reaching the end.  Indicates either pathological contention or
  an invariant violation (panic-equivalent in production). -/
inductive WalkOutcome where
  | extended (newPath : PipChainPath)
  | terminated (finalPath : PipChainPath)
  | exhausted
  deriving Repr

/-- WS-SM SM3.C.11.a: one step of the chain walk.

Given the current path (with `lastTid` as the tail) and the
current SystemState, query `blockingServer s lastTid`.

* `none` → end of chain; return `.terminated path`.
* `some next` with `next.toNat ≤ lastTid.toNat` → return
  `.exhausted` (see modeling note below).
* `some next` with `next.toNat > lastTid.toNat` → extend the path
  with `next`.

The function is single-step (one chain edge); the multi-step
walker iterates it via `walkAndAcquire`.

## Modeling note: ascending-only extension

The `next.toNat > lastTid.toNat` guard means the abstract walker
only commits to a chain step when the next TCB sits at a strictly
*higher* `ObjId.val` than the current tail.  This is a deliberate
**conservative abstraction** of the SM0.I lock-ladder discipline
(plan §5.3 SM3.C.11.a): the deadlock-freedom guarantee
(`walkAndAcquire_path_ascending_in_ObjId_if_terminated`) requires
that every committed acquisition path be strictly `ObjId.val`-
ascending, and this guard enforces exactly that invariant at the
single-step level.

A real PIP blocking chain (following `blockingServer`) is *not*
guaranteed to be `ObjId.val`-ascending — the blocking-graph
topology is independent of the object-store key ordering.  When
the chain is non-ascending, the abstract walker returns
`.exhausted`, which the `withDynamicChainExtension` combinator
treats as "take no dynamic action" (the static lockSet alone is
held).  The FFI-layer runtime (SM5+) handles non-ascending chains
via the optimistic-walk-and-verify retry strategy: discover the
next link, release the current lock, acquire the next at its
`ObjId.val` slot, re-verify — bounded by `MAX_PIP_RETRIES`.  That
runtime mechanism is what makes the walk *complete* (eventually
acquires the full chain); the abstract layer here proves only
*safety* (any committed path is deadlock-free).  Per the plan,
the runtime walker is deferred to SM5+; SM3.C proves the
safety invariant the runtime must preserve. -/
def walkStep (s : SystemState) (path : PipChainPath) : WalkOutcome :=
  match path.path.getLast? with
  | none => .exhausted   -- unreachable under wf_head invariant
  | some lastTid =>
    match blockingServer s lastTid with
    | none => .terminated path
    | some next =>
      if next.toNat > lastTid.toNat then
        let newPath : PipChainPath :=
          { startTid := path.startTid,
            path := path.path ++ [next],
            wf_head := by
              -- Appending to a non-empty list preserves head?.
              have hWf := path.wf_head
              cases hp : path.path with
              | nil =>
                rw [hp] at hWf
                cases hWf
              | cons head tail =>
                show ((head :: tail) ++ [next]).head? = some path.startTid
                simp [List.cons_append, List.head?]
                rw [hp] at hWf
                simp [List.head?] at hWf
                exact hWf }
        .extended newPath
      else
        -- The chain moved backward in ObjId order — invariant violation
        -- or concurrent mutation.  Abort and retry.
        .exhausted

/-- WS-SM SM3.C.11.a: the full chain walker.  Bounded by
`MAX_PIP_RETRIES` to guarantee termination.

Iterates `walkStep` until either:
* The chain terminates naturally (`blockingServer` returns
  `none`), at which point the full path is returned.
* The fuel runs out (we hit `MAX_PIP_RETRIES`), at which point
  `.exhausted` is returned (the production runtime would panic
  on exhaustion; the abstract layer returns the outcome for the
  caller to dispatch). -/
def walkAndAcquire (s : SystemState) (startTid : ThreadId)
    (fuel : Nat := MAX_PIP_RETRIES) : WalkOutcome :=
  walkAndAcquireAux s (PipChainPath.singleton startTid) fuel
where
  walkAndAcquireAux (s : SystemState) (path : PipChainPath) :
      Nat → WalkOutcome
    | 0 => .exhausted
    | Nat.succ n =>
      match walkStep s path with
      | .terminated finalPath => .terminated finalPath
      | .exhausted => .exhausted
      | .extended newPath => walkAndAcquireAux s newPath n

-- ============================================================================
-- §4 — SM3.C.11.c — `dynamicChainHeld` predicate
-- ============================================================================

/-- WS-SM SM3.C.11.c: the adjacent-chain predicate — every
consecutive pair `(a, b)` in the list satisfies `blockingServer s a
= some b`.

A mathlib-free, front-recursive reformulation of "the path follows
the blocking graph" (seLe4n cannot use mathlib's `List.Chain'`).
Induction-friendly: the `_append_of_getLast` lemma below lifts it
across a back-append, which is exactly the shape `walkStep`'s
extension produces.

The empty and singleton lists trivially satisfy it (no adjacent
pair to constrain). -/
def chainFollowsBlockingServer (s : SystemState) : List ThreadId → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      blockingServer s a = some b ∧ chainFollowsBlockingServer s (b :: rest)

/-- WS-SM SM3.C.11.c: `chainFollowsBlockingServer` is decidable —
each adjacent edge `blockingServer s a = some b` is a decidable
`Option ThreadId` equality, composed via `And.decidable` over the
structural recursion.  Enables `decide`-based runtime assertions. -/
instance chainFollowsBlockingServer_decidable (s : SystemState) :
    (l : List ThreadId) → Decidable (chainFollowsBlockingServer s l)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | a :: b :: rest =>
      haveI : Decidable (chainFollowsBlockingServer s (b :: rest)) :=
        chainFollowsBlockingServer_decidable s (b :: rest)
      -- The cons-cons arm reduces definitionally to the conjunction; with
      -- the recursive instance registered (anonymous `haveI`), the
      -- anonymous `Decidable (And _ _)` instance resolves via the
      -- edge-equality's `DecidableEq` and the recursive instance.
      inferInstanceAs (Decidable (blockingServer s a = some b ∧
        chainFollowsBlockingServer s (b :: rest)))

/-- WS-SM SM3.C.11.c: the empty / singleton list trivially follows
the blocking graph. -/
@[simp] theorem chainFollowsBlockingServer_singleton (s : SystemState)
    (tid : ThreadId) : chainFollowsBlockingServer s [tid] := trivial

/-- WS-SM SM3.C.11.c: predicate witnessing that core `c` holds the
write locks on every TCB in `path` on the kernel state `s`.

The four conjuncts:

* `pathHeld`: every TCB in `path` has its lock held by `c` in
  write mode.
* `pathOrdered`: the path is `Pairwise (·.toNat < ·.toNat)` —
  the SM0.I ascending-ObjId discipline.
* `pathStarts`: `path.head? = some startTid` — the path begins
  at the declared start (structurally guaranteed by
  `PipChainPath.wf_head`, restated here so the predicate is
  self-contained).
* `pathChain`: `chainFollowsBlockingServer s path.path` — every
  adjacent pair follows the actual blocking graph.

This is the dynamic counterpart to `lockSetHeld`: the static
lock-set discipline plus this predicate together discharge the
SMP-migration precondition for the 3 PIP-invoking transitions.

**Audit-pass-2**: conjunct 4 reformulated from the indexed
`∀ i, path.path[i] → path.path[i+1]` form to the recursive
`chainFollowsBlockingServer` predicate, which the walker can
establish (see `walkAndAcquire_terminated_satisfies_path_structure`).
The indexed form was a defined-but-unestablished spec; the recursive
form is provably produced by `walkAndAcquire`, wiring this predicate
to its producer. -/
def dynamicChainHeld (c : CoreId) (path : PipChainPath)
    (s : SystemState) : Prop :=
  -- 1. Every TCB in path has its write lock held by c.
  (∀ tid ∈ path.path,
    lockHeld c ⟨.tcb, tid.toObjId⟩ .write s) ∧
  -- 2. ObjId-ascending discipline (SM0.I).
  path.path.Pairwise (fun a b => a.toNat < b.toNat) ∧
  -- 3. Path starts at the declared start.
  path.path.head? = some path.startTid ∧
  -- 4. Path follows the blocking graph (substantive correctness).
  chainFollowsBlockingServer s path.path


-- ============================================================================
-- §5 — SM3.C.11.b — `withDynamicChainExtension` combinator
-- ============================================================================

/-- WS-SM SM3.C.11.b (plan §5.3): the dynamic-chain extension
combinator.

Given:
* `caller` — the core holding the static lockSet.
* `startTid` — the chain start (from `pipChainStart_<τ>`).
* `action` — the chain-walk action (e.g.,
  `propagatePriorityInheritance` or `revertPriorityInheritance`).
* `s` — the post-static-lockSet state (with `startTid`'s TCB lock
  already held).

The combinator (audit-pass-1, Comment 1):
1. Invokes `walkAndAcquire` to discover the chain path.
2. On success (`.terminated path`), **acquires a write lock on
   every TCB in the path** via `acquireAll caller chainLocks`
   (the path is `ObjId.val`-ascending, so this acquire sequence
   respects the SM0.I lock ladder), executes `action` on the
   lock-acquired state, then **releases in reverse order** via
   `releaseAll caller chainLocks.reverse`.
3. On `.exhausted` / `.extended` (no terminating chain), returns
   the input state unchanged with the fallback value.

This closes the Comment-1 gap: the previous form ran `action s`
directly without ever acquiring the chain locks, so the promised
"full chain held" precondition was not established.  The walker
only returned a `WalkOutcome` (the path); the lock acquisition is
now performed explicitly here via the SM3.C.1 `acquireAll` /
`releaseAll` folds, exactly mirroring the static `withLockSet`
2PL discipline but over the dynamically-discovered chain.

The `chainLocks` are all `.tcb`-kinded write locks (the PIP chain
walks the blocking graph of TCBs), built in path order so the
acquire sequence is `ObjId.val`-ascending — deadlock-free by the
same SM0.I total-order argument as the static lock set.

The return value carries:
* The post-release SystemState (or the input if no chain).
* The action's result (or `fallback` if no chain; we parameterize
  on a fallback to keep the combinator total). -/
def withDynamicChainExtension {α : Type} (caller : CoreId)
    (startTid : ThreadId)
    (action : SystemState → SystemState × α)
    (fallback : α) (s : SystemState) : SystemState × α :=
  match walkAndAcquire s startTid with
  | .terminated path =>
      let chainLocks : List (LockId × AccessMode) :=
        path.path.map (fun tid => (⟨.tcb, tid.toObjId⟩, AccessMode.write))
      let acquired := acquireAll caller chainLocks s
      let (postAction, result) := action acquired
      let released := releaseAll caller chainLocks.reverse postAction
      (released, result)
  | .extended _ =>
    -- Walker didn't reach a terminating chain step (still in middle of walk).
    -- At the abstract level, treat as exhausted.
    (s, fallback)
  | .exhausted => (s, fallback)

/-- WS-SM SM3.C.11.b: structural unfolding of
`withDynamicChainExtension`. -/
theorem withDynamicChainExtension_unfold {α : Type} (caller : CoreId)
    (startTid : ThreadId)
    (action : SystemState → SystemState × α)
    (fallback : α) (s : SystemState) :
    withDynamicChainExtension caller startTid action fallback s =
      (match walkAndAcquire s startTid with
       | .terminated path =>
           let chainLocks : List (LockId × AccessMode) :=
             path.path.map (fun tid => (⟨.tcb, tid.toObjId⟩, AccessMode.write))
           let acquired := acquireAll caller chainLocks s
           let (postAction, result) := action acquired
           let released := releaseAll caller chainLocks.reverse postAction
           (released, result)
       | .extended _ => (s, fallback)
       | .exhausted => (s, fallback)) := rfl

-- ============================================================================
-- §6 — SM3.C.11.d — Deadlock-freedom for dynamic chain
-- ============================================================================

/-- WS-SM SM3.C.11.d: helper — every chain step strictly increases
the `ObjId.val` of the latest TCB.

Follows from `walkStep`'s `next.toNat > lastTid.toNat` guard: an
`.extended` outcome only fires when the next chain link is at
strictly higher `ObjId.val`. -/
theorem walkStep_extended_increases_objId (s : SystemState) (path : PipChainPath)
    (newPath : PipChainPath)
    (h : walkStep s path = .extended newPath) :
    ∃ lastTid newTid, path.path.getLast? = some lastTid ∧
      newPath.path = path.path ++ [newTid] ∧
      newTid.toNat > lastTid.toNat := by
  unfold walkStep at h
  split at h
  next hLast =>
    -- getLast? = none branch
    cases h
  next lastTid hLast =>
    -- getLast? = some lastTid branch
    split at h
    next hBs =>
      -- blockingServer = none branch → .terminated
      cases h
    next next hBs =>
      -- blockingServer = some next branch
      split at h
      next hGt =>
        -- next.toNat > lastTid.toNat → .extended branch
        injection h with hEq
        refine ⟨lastTid, next, hLast, ?_, hGt⟩
        rw [← hEq]
      next _hNotGt =>
        -- next.toNat ≤ lastTid.toNat → .exhausted branch
        cases h

/-- WS-SM SM3.C.11.d helper: if appending `b` to a list `l` whose
`getLast?` is `some a` preserves the strict-ascending Pairwise
property, provided `a.toNat < b.toNat`.

Proof strategy: use `List.getLast?_eq_some_iff` to rewrite
`l = ys ++ [a]`.  Then `l ++ [b] = ys ++ [a] ++ [b] = ys ++ [a, b]`.
The Pairwise on `l` provides the Pairwise on `ys ++ [a]`; we need
to extend with the additional element `b`.  Use
`List.pairwise_append` decomposition and rely on the fact that
every `x ∈ ys` satisfies `x.toNat < a.toNat` (from the original
Pairwise on `ys ++ [a]`) which combined with `a.toNat < b.toNat`
gives `x.toNat < b.toNat`. -/
private theorem pairwise_append_singleton_of_last
    (l : List ThreadId) (a b : ThreadId)
    (hLast : l.getLast? = some a)
    (hPairwise : l.Pairwise (fun x y => x.toNat < y.toNat))
    (hLt : a.toNat < b.toNat) :
    (l ++ [b]).Pairwise (fun x y => x.toNat < y.toNat) := by
  -- Rewrite l using getLast?_eq_some_iff.
  obtain ⟨ys, hYs⟩ := List.getLast?_eq_some_iff.mp hLast
  rw [hYs]
  -- Goal: (ys ++ [a] ++ [b]).Pairwise (·.toNat < ·.toNat).
  -- Rewrite append associativity.
  rw [List.append_assoc]
  -- Goal: (ys ++ ([a] ++ [b])).Pairwise (·.toNat < ·.toNat).
  -- Apply pairwise_append: needs Pairwise ys, Pairwise [a,b], and forall x∈ys, y∈[a,b], x < y.
  rw [List.pairwise_append]
  -- Get Pairwise on ys from hPairwise (Pairwise on ys ++ [a]).
  rw [hYs] at hPairwise
  rw [List.pairwise_append] at hPairwise
  obtain ⟨hPwYs, hPwA, hCross⟩ := hPairwise
  refine ⟨hPwYs, ?_, ?_⟩
  · -- [a, b] is Pairwise.
    show ([a] ++ [b]).Pairwise (fun x y => x.toNat < y.toNat)
    rw [List.pairwise_append]
    refine ⟨hPwA, ?_, ?_⟩
    · -- [b] is Pairwise.
      exact List.Pairwise.cons (fun _ h => by cases h) List.Pairwise.nil
    · intro x hxIn y hyIn
      cases hxIn with
      | head =>
        cases hyIn with
        | head => exact hLt
        | tail _ hContra => cases hContra
      | tail _ hContra => cases hContra
  · -- For x ∈ ys and y ∈ [a, b]: x.toNat < y.toNat.
    intro x hxIn y hyIn
    -- We have hCross: ∀ x ∈ ys, ∀ y ∈ [a], x.toNat < y.toNat.
    -- That gives us x.toNat < a.toNat (specialised to y = a).
    have hxLtA : x.toNat < a.toNat := by
      apply hCross x hxIn
      simp
    cases hyIn with
    | head =>
      -- y = a.
      exact hxLtA
    | tail _ hyIn' =>
      cases hyIn' with
      | head =>
        -- y = b; combine x < a < b.
        exact Nat.lt_trans hxLtA hLt
      | tail _ hContra => cases hContra

/-- WS-SM SM3.C.11.d helper: `walkStep` extends a strictly-
ascending path with a strictly-greater element. -/
private theorem walkStep_preserves_ascending
    (s : SystemState) (path : PipChainPath)
    (newPath : PipChainPath)
    (h : walkStep s path = .extended newPath)
    (hAsc : path.path.Pairwise (fun a b => a.toNat < b.toNat)) :
    newPath.path.Pairwise (fun a b => a.toNat < b.toNat) := by
  obtain ⟨lastTid, newTid, hLast, hNew, hLt⟩ :=
    walkStep_extended_increases_objId s path newPath h
  rw [hNew]
  exact pairwise_append_singleton_of_last path.path lastTid newTid hLast hAsc hLt

/-- WS-SM SM3.C.11.d helper: `walkStep` returns `.terminated finalPath`
only when the chain ends (blockingServer returns `none`).  In that
case the returned path is the input path unchanged. -/
private theorem walkStep_terminated_path_unchanged
    (s : SystemState) (path : PipChainPath)
    (finalPath : PipChainPath)
    (h : walkStep s path = .terminated finalPath) :
    finalPath = path := by
  unfold walkStep at h
  split at h
  · -- getLast? = none branch
    cases h
  · -- getLast? = some lastTid branch
    split at h
    · -- blockingServer = none branch → .terminated
      injection h with hEq
      exact hEq.symm
    · -- blockingServer = some next branch
      split at h
      · -- > branch → .extended
        cases h
      · -- ≤ branch → .exhausted
        cases h

/-- WS-SM SM3.C.11.d (plan §5.3): the SM0.I total-order ascending
discipline.  Any successful chain walk produces a path whose
ObjIds are strictly ascending — the same discipline as the static
2PL lockSet's `lockAcquireSequence`.

This means two cores walking different chains cannot deadlock:
each only ever holds locks at strictly ascending `ObjId.val`, so
no cycle in the wait-graph can form (by the SM0.I total-order
contradiction). -/
theorem walkAndAcquire_path_ascending_in_ObjId_if_terminated
    (s : SystemState) (startTid : ThreadId) (fuel : Nat)
    (path : PipChainPath)
    (h : walkAndAcquire.walkAndAcquireAux s (PipChainPath.singleton startTid) fuel
      = .terminated path) :
    -- The path is ascending in ObjId.val (the SM0.I discipline).
    path.path.Pairwise (fun a b => a.toNat < b.toNat) := by
  -- The path starts as singleton (trivially Pairwise), and every
  -- walkStep extension preserves strict ascending order via
  -- walkStep_preserves_ascending.  We induct on fuel with a
  -- generalised version that tracks the accumulated path.
  have hAux : ∀ (fuel' : Nat) (path₀ path' : PipChainPath),
      path₀.path.Pairwise (fun a b => a.toNat < b.toNat) →
      walkAndAcquire.walkAndAcquireAux s path₀ fuel' = .terminated path' →
      path'.path.Pairwise (fun a b => a.toNat < b.toNat) := by
    intro fuel'
    induction fuel' with
    | zero =>
      intro path₀ path' _hAsc hWalk
      simp [walkAndAcquire.walkAndAcquireAux] at hWalk
    | succ n ih =>
      intro path₀ path' hAsc hWalk
      -- Unfold walkAndAcquireAux at succ.
      unfold walkAndAcquire.walkAndAcquireAux at hWalk
      cases hStep : walkStep s path₀ with
      | terminated finalPath =>
        rw [hStep] at hWalk
        -- hWalk now : finalPath = path' (.terminated injectivity).
        injection hWalk with hEq
        -- The terminated branch returns the path unchanged; so path' = path₀.
        have hUnchanged := walkStep_terminated_path_unchanged s path₀ finalPath hStep
        rw [← hEq, hUnchanged]
        exact hAsc
      | exhausted =>
        rw [hStep] at hWalk
        cases hWalk
      | extended newPath =>
        rw [hStep] at hWalk
        have hNewAsc := walkStep_preserves_ascending s path₀ newPath hStep hAsc
        exact ih newPath path' hNewAsc hWalk
  -- Apply hAux to the initial singleton path.
  apply hAux fuel (PipChainPath.singleton startTid) path
  · -- The singleton list is trivially Pairwise.
    simp [PipChainPath.singleton]
  · exact h

-- ============================================================================
-- §7 — SM3.C.11.e — Termination under bounded retries
-- ============================================================================

/-- WS-SM SM3.C.11.e helper: a `.extended` step grows the path
length by exactly one.  Follows from `walkStep_extended_increases_objId`
(the new path is the old path with one element appended). -/
private theorem walkStep_extended_length (s : SystemState) (path : PipChainPath)
    (newPath : PipChainPath)
    (h : walkStep s path = .extended newPath) :
    newPath.path.length = path.path.length + 1 := by
  obtain ⟨_lastTid, _newTid, _hLast, hNew, _hLt⟩ :=
    walkStep_extended_increases_objId s path newPath h
  rw [hNew, List.length_append]
  simp

/-- WS-SM SM3.C.11.e (plan §5.3): termination under bounded
retries.  `walkAndAcquire` is a total function (Lean's
structural-recursion checker accepts the `fuel`-decreasing
definition, so every call returns a `WalkOutcome` — that totality
*is* the termination guarantee).  This theorem records the
explicit boundedness witness the plan's
`walkAndAcquire_terminates` calls for: if the walk *terminates*
with a path, that path's length is bounded by the fuel budget
plus the initial singleton — so a chain longer than
`MAX_PIP_RETRIES + 1` exhausts the budget (returns `.exhausted`)
rather than looping forever.

The bound is `initialPath.length + fuel`: the walker starts from
a path of some length and each `.extended` step both grows the
path by one (`walkStep_extended_length`) and consumes one fuel
unit, so after `fuel` steps the path can have grown by at most
`fuel`. -/
theorem walkAndAcquireAux_terminated_length_le (s : SystemState)
    (initialPath : PipChainPath) (fuel : Nat) (finalPath : PipChainPath)
    (h : walkAndAcquire.walkAndAcquireAux s initialPath fuel
      = .terminated finalPath) :
    finalPath.path.length ≤ initialPath.path.length + fuel := by
  induction fuel generalizing initialPath with
  | zero =>
    -- fuel = 0 ⇒ .exhausted, contradicting .terminated.
    simp [walkAndAcquire.walkAndAcquireAux] at h
  | succ n ih =>
    unfold walkAndAcquire.walkAndAcquireAux at h
    cases hStep : walkStep s initialPath with
    | terminated fp =>
      rw [hStep] at h
      injection h with hEq
      -- terminated returns the path unchanged.
      have hUnchanged := walkStep_terminated_path_unchanged s initialPath fp hStep
      rw [← hEq, hUnchanged]
      omega
    | exhausted =>
      rw [hStep] at h
      cases h
    | extended newPath =>
      rw [hStep] at h
      have hLen := walkStep_extended_length s initialPath newPath hStep
      have hRec := ih newPath h
      rw [hLen] at hRec
      omega

/-- WS-SM SM3.C.11.e: the top-level boundedness witness.  A
terminating `walkAndAcquire` produces a path of length at most
`MAX_PIP_RETRIES + 1` (the chain depth is bounded by the retry
budget).  Combined with the totality of `walkAndAcquire` (a
structural-recursion-checked total function), this is the
explicit termination guarantee the plan's SM3.C.11.e
`walkAndAcquire_terminates` calls for. -/
theorem walkAndAcquire_terminated_length_bounded (s : SystemState)
    (startTid : ThreadId) (finalPath : PipChainPath)
    (h : walkAndAcquire s startTid = .terminated finalPath) :
    finalPath.path.length ≤ MAX_PIP_RETRIES + 1 := by
  unfold walkAndAcquire at h
  have hLe := walkAndAcquireAux_terminated_length_le s
    (PipChainPath.singleton startTid) MAX_PIP_RETRIES finalPath h
  simp [PipChainPath.singleton] at hLe
  omega

/-- WS-SM SM3.C.11.e: totality witness — `walkAndAcquire` returns a
value for every input (it never diverges).  Trivial because the
function is total (Lean's `fuel`-decreasing structural recursion),
but recorded explicitly as the SM3.C.11.e termination anchor. -/
theorem walkAndAcquire_total (s : SystemState) (startTid : ThreadId)
    (fuel : Nat) :
    ∃ outcome, walkAndAcquire.walkAndAcquireAux s
      (PipChainPath.singleton startTid) fuel = outcome :=
  ⟨_, rfl⟩

-- ============================================================================
-- §8 — SM3.C.11.c — Walker establishes the dynamicChainHeld path structure
-- ============================================================================
--
-- These theorems WIRE the `dynamicChainHeld` predicate to its producer
-- (`walkAndAcquire`).  Without them `dynamicChainHeld` would be an
-- orphan spec — defined but never shown to be establishable.  They
-- prove the walker's terminated path satisfies the three *structural*
-- conjuncts of `dynamicChainHeld` (ascending, starts-at-start, follows-
-- blocking-graph).  The fourth conjunct (every TCB write-locked) is the
-- separate job of `withDynamicChainExtension`'s `acquireAll` over the
-- chain locks — it is a property of the lock-acquired state, not of the
-- walker's pure path discovery.

/-- WS-SM SM3.C.11.c helper: `walkStep` on an `.extended` outcome
exposes the blocking-graph edge it traversed: the tail `lastTid`,
the new link `newTid`, and the fact `blockingServer s lastTid =
some newTid` (the edge the step followed).  Richer companion to
`walkStep_extended_increases_objId`. -/
theorem walkStep_extended_blockingServer (s : SystemState) (path : PipChainPath)
    (newPath : PipChainPath)
    (h : walkStep s path = .extended newPath) :
    ∃ lastTid newTid, path.path.getLast? = some lastTid ∧
      newPath.path = path.path ++ [newTid] ∧
      blockingServer s lastTid = some newTid := by
  unfold walkStep at h
  split at h
  next hLast => cases h
  next lastTid hLast =>
    split at h
    next hBs => cases h
    next next hBs =>
      split at h
      next _hGt =>
        injection h with hEq
        refine ⟨lastTid, next, hLast, ?_, hBs⟩
        rw [← hEq]
      next _hNotGt => cases h

/-- WS-SM SM3.C.11.c helper: appending `b` to a list `l` whose
`getLast?` is `some a` preserves `chainFollowsBlockingServer`,
provided the edge `blockingServer s a = some b` holds.

Proved by induction on `l` — same back-append shape as
`pairwise_append_singleton_of_last`.  The front-recursive predicate
recurses past the head until the singleton tail, where the new edge
`a → b` is discharged by `hEdge`. -/
private theorem chainFollowsBlockingServer_append_of_getLast
    (s : SystemState) (l : List ThreadId) (a b : ThreadId)
    (hLast : l.getLast? = some a)
    (hChain : chainFollowsBlockingServer s l)
    (hEdge : blockingServer s a = some b) :
    chainFollowsBlockingServer s (l ++ [b]) := by
  induction l with
  | nil => cases hLast
  | cons head tail ih =>
    -- Substituting `cases` on `tail` specialises `ih` to the cons tail.
    cases tail with
    | nil =>
      -- l = [head]; getLast? = some head ⇒ a = head; result = [head, b].
      simp only [List.getLast?_singleton, Option.some.injEq] at hLast
      subst hLast
      -- chainFollowsBlockingServer s ([head] ++ [b]) = (edge head→b) ∧ True
      exact ⟨hEdge, trivial⟩
    | cons head₂ tail₂ =>
      -- hChain : blockingServer s head = some head₂ ∧ chainFollowsBlockingServer s (head₂ :: tail₂)
      obtain ⟨hEdgeHead, hChainTail⟩ := hChain
      have hLastTail : (head₂ :: tail₂).getLast? = some a := by
        rw [List.getLast?_cons_cons] at hLast; exact hLast
      -- ih (now about head₂ :: tail₂) gives chain ((head₂::tail₂) ++ [b]).
      have hRec := ih hLastTail hChainTail
      -- Goal: chain (head :: head₂ :: (tail₂ ++ [b])).
      exact ⟨hEdgeHead, hRec⟩

/-- WS-SM SM3.C.11.c helper: `walkStep`'s `.extended` step preserves
`chainFollowsBlockingServer`.  The new path is the old path with the
traversed edge's target appended, and the edge follows the blocking
graph (`walkStep_extended_blockingServer`), so the append lemma
applies. -/
private theorem walkStep_extended_preserves_chain (s : SystemState)
    (path : PipChainPath) (newPath : PipChainPath)
    (h : walkStep s path = .extended newPath)
    (hChain : chainFollowsBlockingServer s path.path) :
    chainFollowsBlockingServer s newPath.path := by
  obtain ⟨lastTid, newTid, hLast, hNew, hEdge⟩ :=
    walkStep_extended_blockingServer s path newPath h
  rw [hNew]
  exact chainFollowsBlockingServer_append_of_getLast s path.path lastTid newTid
    hLast hChain hEdge

/-- WS-SM SM3.C.11.c: a terminating walk produces a path that
follows the blocking graph (`chainFollowsBlockingServer`).  Proved
by induction on the retry fuel, mirroring
`walkAndAcquire_path_ascending_in_ObjId_if_terminated`: the singleton
seed trivially follows the graph, and every `.extended` step
preserves the property (`walkStep_extended_preserves_chain`). -/
theorem walkAndAcquire_terminated_followsChain
    (s : SystemState) (startTid : ThreadId) (fuel : Nat)
    (path : PipChainPath)
    (h : walkAndAcquire.walkAndAcquireAux s (PipChainPath.singleton startTid) fuel
      = .terminated path) :
    chainFollowsBlockingServer s path.path := by
  have hAux : ∀ (fuel' : Nat) (path₀ path' : PipChainPath),
      chainFollowsBlockingServer s path₀.path →
      walkAndAcquire.walkAndAcquireAux s path₀ fuel' = .terminated path' →
      chainFollowsBlockingServer s path'.path := by
    intro fuel'
    induction fuel' with
    | zero =>
      intro path₀ path' _hChain hWalk
      simp [walkAndAcquire.walkAndAcquireAux] at hWalk
    | succ n ih =>
      intro path₀ path' hChain hWalk
      unfold walkAndAcquire.walkAndAcquireAux at hWalk
      cases hStep : walkStep s path₀ with
      | terminated fp =>
        rw [hStep] at hWalk
        injection hWalk with hEq
        have hUnchanged := walkStep_terminated_path_unchanged s path₀ fp hStep
        rw [← hEq, hUnchanged]
        exact hChain
      | exhausted =>
        rw [hStep] at hWalk; cases hWalk
      | extended newPath =>
        rw [hStep] at hWalk
        have hNewChain := walkStep_extended_preserves_chain s path₀ newPath hStep hChain
        exact ih newPath path' hNewChain hWalk
  apply hAux fuel (PipChainPath.singleton startTid) path
  · simp [PipChainPath.singleton]
  · exact h

/-- WS-SM SM3.C.11.c (plan §5.3): the walker establishes the
**path-structure** conjuncts of `dynamicChainHeld`.

Bundles the three structural properties a terminating
`walkAndAcquire` produces:
* conjunct 2 — `ObjId.val`-ascending
  (`walkAndAcquire_path_ascending_in_ObjId_if_terminated`),
* conjunct 3 — starts at `startTid` (`PipChainPath.wf_head`),
* conjunct 4 — follows the blocking graph
  (`walkAndAcquire_terminated_followsChain`).

This is the producer-side connection that wires `dynamicChainHeld`
to `walkAndAcquire`: the walker's output IS a valid ascending
blocking-chain rooted at `startTid`.  The remaining conjunct 1
(every TCB write-locked) is established by
`withDynamicChainExtension`'s `acquireAll` over the chain locks,
not by the walker's pure path discovery — so it is intentionally
not part of this walker theorem. -/
theorem walkAndAcquire_terminated_satisfies_path_structure
    (s : SystemState) (startTid : ThreadId) (fuel : Nat)
    (path : PipChainPath)
    (h : walkAndAcquire.walkAndAcquireAux s (PipChainPath.singleton startTid) fuel
      = .terminated path) :
    path.path.Pairwise (fun a b => a.toNat < b.toNat) ∧
    path.path.head? = some path.startTid ∧
    chainFollowsBlockingServer s path.path :=
  ⟨walkAndAcquire_path_ascending_in_ObjId_if_terminated s startTid fuel path h,
   path.wf_head,
   walkAndAcquire_terminated_followsChain s startTid fuel path h⟩

end SeLe4n.Kernel.Concurrency
