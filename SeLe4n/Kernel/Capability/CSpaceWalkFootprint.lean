-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-RR RR7.41: PRODUCTION.  The multi-level CSpace resolution's footprint —
-- a read lock on every CNode the walk passes through, not just the root.

import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.Concurrency.Locks.LockSetTransitions
import SeLe4n.Kernel.Concurrency.Locks.Serializability
import SeLe4n.Kernel.SyscallLockBracket

/-!
# WS-RR RR7.41 — the interior of a CSpace walk

`resolveCapAddress` descends through child CNodes while address bits remain, and
every per-object footprint in the tree names only the walk's **root**
(`cnodeLock cnodeRootObjId`), because the interior is discovered from the guard
and radix of each CNode the walk reads and so cannot be named from the
arguments.  A concurrent `cspaceDelete` of an interior slot therefore had no
conflicting lock against a resolution passing through it — the state
`UncoveredLockDomain.cspaceWalkInteriorCnodes` recorded.

## The shape, and why it is not hand-over-hand

The obvious remedy is lock-coupling: acquire the child's read lock before
releasing the parent's, walking down.  This cut does something else, and the
difference is deliberate.

Hand-over-hand coupling holds at most two locks but abandons the **global lock
order**: the walk descends the CSpace graph, whose edges do not follow
`ObjId.val`, so a coupling walk acquires out of ladder order and needs its own
deadlock-freedom argument over the capability graph — an argument that would then
have to be maintained against every future capability operation.  The whole
tree's deadlock freedom instead rests on one total order (SM0.I), and nothing
else in the kernel departs from it.

So the walk keeps the ladder and pays for it with a *revalidation* instead:
resolve the path, acquire the read locks **sorted** into ladder order, re-resolve
under them, and refuse if the path moved.  That is exactly RR7.12's discipline —
`runUnderDeclaredLockSet` — applied to a footprint discovered by a walk rather
than read off an argument, and it is available precisely because the bracket was
already generic in how its footprint is resolved.  The exclusion obtained is the
same one coupling would give (§3), and the acquisition order is the one the rest
of the kernel uses.

Read locks, not write: a resolution reads the interior and writes nothing.  Two
concurrent resolutions through the same CNode therefore do not exclude each
other, which is what makes the wider footprint affordable.

## Why nothing is owed at the live seam

`lockSetForSyscall`'s arms name the root alone, and that is **complete** rather
than approximate — §3b proves it.  RR7.12's `abiEntryGate` admits a resolution
only when `rootCn.depth = rootCn.guardWidth + rootCn.radixWidth`, so the root
consumes every address bit and `resolveCapAddress` reaches its leaf arm on the
first hop; `cspaceWalkPath_single_level` says the walk is then exactly
`[rootId]`, and `cspaceWalkLockSet_single_level` that the footprint is exactly
the root's read lock.  A multi-level walk, for which a root-only footprint
genuinely would be false, is one the seam declares no footprint for at all — it
falls back to the coarser serialisation, which is always sound.

So the registry entry goes because the domain is *covered*, not deferred: at the
live seam by the single-level theorem, and anywhere a future consumer wants to
admit a multi-level walk by `cspaceWalkLockSet` and the conflict result in §3.
Both halves are proved here; neither is owed.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (LockId LockSet AccessMode CoreId cnodeLock lockSetOfList
  ktiSharesConflictingLock)

-- ============================================================================
-- §1  The path a resolution walks
-- ============================================================================

/-- **WS-RR RR7.41**: the object-store keys a multi-level resolution **reads**,
root first — every CNode it passes through and, when the walk ends on a key
that holds no CNode, that key too.

Derived from the **same** recursion `resolveCapAddress` runs — same guard check,
same radix split, same child selection, same `bitsRemaining` descent — because a
footprint resolved from a different walk is a footprint for a different
resolution.  Every arm on which `resolveCapAddress` gives up yields the keys
read so far, which is the fail-closed direction: a refused resolution still
read the keys it reached, so its footprint must still name them.

**A failed lookup is a read** (PR #892 review round 4).  `resolveCapAddress`
reads the store at the root, and at every child it selects, *before* it knows
whether a CNode is there; when the key is absent or holds another kind of
object the resolution fails, and its outcome depended on that key's state.  The
first cut returned `[]` on that arm — the key was read and the footprint did
not name it, so a concurrent retype or deletion at exactly that key shared no
lock with the resolution and could change its verdict between the bracket's
revalidation and its walk.  The key is now on the path, and
`cspaceWalkKeyLock` says which lock it declares. -/
def cspaceWalkPath (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (bitsRemaining : Nat)
    (st : SystemState) : List SeLe4n.ObjId :=
  if hZero : bitsRemaining = 0 then []
  else
    match st.getCNode? rootId with
    | none => [rootId]
    | some cn =>
      let consumed := cn.guardWidth + cn.radixWidth
      if hCons : consumed = 0 then [rootId]
      else if bitsRemaining < consumed then [rootId]
      else
        let maskedAddr := addr.toNat % SeLe4n.machineWordMax
        let shiftedAddr := maskedAddr >>> (bitsRemaining - consumed)
        let radixMask := 2 ^ cn.radixWidth
        let slotIndex := shiftedAddr % radixMask
        let guardExtracted := (shiftedAddr / radixMask) % (2 ^ cn.guardWidth)
        if guardExtracted ≠ cn.guardValue then [rootId]
        else if bitsRemaining - consumed = 0 then [rootId]
        else
          match cn.lookup (SeLe4n.Slot.ofNat slotIndex) with
          | some cap =>
            match cap.target with
            | .object childId =>
              have hConsPos : consumed > 0 := Nat.pos_of_ne_zero hCons
              have hBitsPos : bitsRemaining > 0 := Nat.pos_of_ne_zero hZero
              have : bitsRemaining - consumed < bitsRemaining := Nat.sub_lt hBitsPos hConsPos
              rootId :: cspaceWalkPath childId addr (bitsRemaining - consumed) st
            | _ => [rootId]
          | none => [rootId]
  termination_by bitsRemaining

/-- **WS-RR RR7.41**: a walk with bits remaining and a resolvable root begins at
that root — so the footprint always names the CNode the caller supplied, and the
existing root-only footprints are contained in this one. -/
theorem cspaceWalkPath_head (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr)
    (bitsRemaining : Nat) (st : SystemState) (cn : CNode)
    (hBits : bitsRemaining ≠ 0) (hRoot : st.getCNode? rootId = some cn) :
    rootId ∈ cspaceWalkPath rootId addr bitsRemaining st := by
  unfold cspaceWalkPath
  rw [dif_neg hBits, hRoot]
  simp only
  split
  · exact List.mem_singleton.mpr rfl
  · split
    · exact List.mem_singleton.mpr rfl
    · split
      · exact List.mem_singleton.mpr rfl
      · split
        · exact List.mem_singleton.mpr rfl
        · split
          · split
            · exact List.mem_cons_self
            · exact List.mem_singleton.mpr rfl
          · exact List.mem_singleton.mpr rfl

/-- **WS-RR RR7.41**: a zero-bit walk reads no CNode and declares nothing — the
`.illegalState` arm `resolveCapAddress` takes first. -/
@[simp] theorem cspaceWalkPath_zero (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr)
    (st : SystemState) : cspaceWalkPath rootId addr 0 st = [] := by
  unfold cspaceWalkPath; rw [dif_pos rfl]

/-- **WS-RR RR7.41 / PR #892 review round 4**: an unresolvable root is still
*read* — the `.objectNotFound` arm looked the key up — so the walk names it and
nothing else.  (The first cut returned `[]` here, which declared no lock for a
read the resolution's verdict depended on.) -/
theorem cspaceWalkPath_no_root (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr)
    (bitsRemaining : Nat) (st : SystemState) (hBits : bitsRemaining ≠ 0)
    (h : st.getCNode? rootId = none) :
    cspaceWalkPath rootId addr bitsRemaining st = [rootId] := by
  unfold cspaceWalkPath
  rw [dif_neg hBits, h]

/-- **PR #892 review round 4**: a walk with bits remaining begins at its root
*whatever the root holds* — a resolvable root continues (or stops) there, an
unresolvable one records the key it read.  `cspaceWalkPath_head` is the
resolvable half; this is the shape the interior theorem below recurses on. -/
theorem cspaceWalkPath_cons (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr)
    (bitsRemaining : Nat) (st : SystemState) (hBits : bitsRemaining ≠ 0) :
    ∃ rest, cspaceWalkPath rootId addr bitsRemaining st = rootId :: rest := by
  unfold cspaceWalkPath
  rw [dif_neg hBits]
  cases hRoot : st.getCNode? rootId with
  | none => exact ⟨[], rfl⟩
  | some cn =>
    simp only
    split
    · exact ⟨[], rfl⟩
    · split
      · exact ⟨[], rfl⟩
      · split
        · exact ⟨[], rfl⟩
        · split
          · exact ⟨[], rfl⟩
          · split
            · split
              · exact ⟨_, rfl⟩
              · exact ⟨[], rfl⟩
            · exact ⟨[], rfl⟩

/-- **PR #892 review round 4**: every key on the path **before the last** holds
a CNode — the walk continued through it — so a key holding no CNode can only be
the path's last key, the one the failed lookup read.  Two consequences the
footprint rests on: a walk declares at most **one** state-level member, and the
CNode read locks it declares are exactly the interior it passed through.  By
strong induction on the bits remaining, which is what the walk recurses on. -/
theorem cspaceWalkPath_dropLast_cnode (addr : SeLe4n.CPtr) (st : SystemState) :
    ∀ (bitsRemaining : Nat) (rootId oid : SeLe4n.ObjId),
      oid ∈ (cspaceWalkPath rootId addr bitsRemaining st).dropLast →
      (st.getCNode? oid).isSome := by
  intro bitsRemaining
  induction bitsRemaining using Nat.strongRecOn with
  | ind bitsRemaining ih =>
  intro rootId oid hMem
  by_cases hZero : bitsRemaining = 0
  · subst hZero
    simp at hMem
  · rw [cspaceWalkPath, dif_neg hZero] at hMem
    cases hRoot : st.getCNode? rootId with
    | none =>
      rw [hRoot] at hMem
      simp at hMem
    | some cn =>
      rw [hRoot] at hMem
      simp only at hMem
      split at hMem
      · simp at hMem
      · split at hMem
        · simp at hMem
        · split at hMem
          · simp at hMem
          · split at hMem
            · simp at hMem
            · split at hMem
              · split at hMem
                · rename_i childId _
                  by_cases hRest : bitsRemaining - (cn.guardWidth + cn.radixWidth) = 0
                  · rw [hRest, cspaceWalkPath_zero] at hMem
                    simp at hMem
                  · obtain ⟨rest, hPath⟩ :=
                      cspaceWalkPath_cons childId addr
                        (bitsRemaining - (cn.guardWidth + cn.radixWidth)) st hRest
                    rw [hPath] at hMem
                    simp only [List.dropLast, List.mem_cons] at hMem
                    rcases hMem with rfl | hMem
                    · rw [hRoot]; rfl
                    · rw [← hPath] at hMem
                      exact ih (bitsRemaining - (cn.guardWidth + cn.radixWidth))
                        (by omega) childId oid hMem
                · simp at hMem
              · simp at hMem

-- ============================================================================
-- §2  The footprint
-- ============================================================================

/-- **PR #892 review round 4**: the lock a key on the walk's path declares.

A key holding a CNode declares that CNode's **read** lock — the interior lock
RR7.41 introduced.  A key holding **no CNode** (absent, or another kind of
object) declares the **state-level** lock in read mode: no per-object lock can
stand for a key with nothing behind it, and the writers that can change what a
key holds — a retype installing an object there, a `cspaceDelete` or a cleanup
removing one — are the *structural* writers, every one of which declares
`stateLevelLock` in **write** mode (`lockSet_lifecycleRetype`,
`lockSet_cspaceDelete`).  Read against write conflicts, so a resolution that
failed at a key and a writer that would make it succeed are ordered by SM3.E's
conflict relation rather than interleaved.  A lock of the object's *actual*
kind would not do: the resolution does not know the kind, and a `cnodeLock` at a
key holding a TCB is a different `LockId` from the TCB's own. -/
def cspaceWalkKeyLock (st : SystemState) (oid : SeLe4n.ObjId) : LockId × AccessMode :=
  match st.getCNode? oid with
  | some _ => (cnodeLock oid, AccessMode.read)
  | none => (Concurrency.stateLevelLock, AccessMode.read)

/-- **WS-RR RR7.41**: the footprint a multi-level resolution declares — a
**read** lock on every CNode it passes through, and (PR #892 review round 4)
the state-level read lock when it ends on a key holding no CNode.

`lockSetOfList` merges duplicate keys, so a walk that revisits a CNode (which the
capability graph permits) names it once, and `LockSet.lockAcquireSequence` sorts
the result into the SM0.I ladder order the bracket acquires in.  The walk's own
order is the CSpace's, which is not the ladder's — sorting is what lets the
existing deadlock-freedom argument carry, and is why this is a revalidating
bracket rather than a coupling walk. -/
def cspaceWalkLockSet (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (bitsRemaining : Nat)
    (st : SystemState) : LockSet :=
  lockSetOfList ((cspaceWalkPath rootId addr bitsRemaining st).map (cspaceWalkKeyLock st))

/-- **WS-RR RR7.41**: the resolution's declared footprint, in the shape the
bracket takes.

Every walk whose footprint fits the ceiling declares one, the empty walk
included (its footprint is empty and its bracket acquires nothing).  The one
`none` arm is the **ceiling** (PR #892 review round 4): a walk consumes at
least one address bit per CNode, so a path can visit up to one distinct CNode
per address bit — far more than `maxLockSetSize`, and `boundedWait_under_2pl`,
the `KernelOperation` invariant and the WCRT surface all take
`S.size ≤ maxLockSetSize` as their premise.  A footprint above it handed to
the bracket would be acquired in full and reasoned about by nothing, and the
bound census (`SeLe4n/Testing/LockFootprintBoundCensus.lean`) could not see
it: that census requires an *unconditional* bound of every `lockSet_…`
declaration, and this footprint has none — its bound is the refusal.  So a walk
above the ceiling declares nothing, and the bracket falls back to the coarser
serialisation, which is always sound
(`declaredLockSetForCSpaceWalk_some_size_le`, `…_none_of_gt`). -/
def declaredLockSetForCSpaceWalk (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr)
    (bitsRemaining : Nat) : SystemState → Option LockSet :=
  fun st =>
    let S := cspaceWalkLockSet rootId addr bitsRemaining st
    if S.size ≤ Concurrency.maxLockSetSize then some S else none

/-- **PR #892 review round 4**: every footprint the walk *declares* is within
the ceiling — the premise the bounded-wait and WCRT results take, discharged at
the one place a walk-derived footprint reaches the bracket. -/
theorem declaredLockSetForCSpaceWalk_some_size_le (rootId : SeLe4n.ObjId)
    (addr : SeLe4n.CPtr) (bitsRemaining : Nat) (st : SystemState) (S : LockSet)
    (h : declaredLockSetForCSpaceWalk rootId addr bitsRemaining st = some S) :
    S.size ≤ Concurrency.maxLockSetSize := by
  unfold declaredLockSetForCSpaceWalk at h
  simp only at h
  split at h
  · rename_i hLe
    injection h with hS
    rw [← hS]; exact hLe
  · cases h

/-- **PR #892 review round 4**: a walk within the ceiling declares exactly its
footprint. -/
theorem declaredLockSetForCSpaceWalk_of_le (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr)
    (bitsRemaining : Nat) (st : SystemState)
    (h : (cspaceWalkLockSet rootId addr bitsRemaining st).size ≤ Concurrency.maxLockSetSize) :
    declaredLockSetForCSpaceWalk rootId addr bitsRemaining st
      = some (cspaceWalkLockSet rootId addr bitsRemaining st) := by
  unfold declaredLockSetForCSpaceWalk
  simp only [h, if_true]

/-- **PR #892 review round 4 (the load-bearing negative)**: a walk above the
ceiling declares **nothing**, so the bracket takes its undeclared arm rather
than acquiring a footprint the bounded-wait reasoning is silent about. -/
theorem declaredLockSetForCSpaceWalk_none_of_gt (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr)
    (bitsRemaining : Nat) (st : SystemState)
    (h : Concurrency.maxLockSetSize < (cspaceWalkLockSet rootId addr bitsRemaining st).size) :
    declaredLockSetForCSpaceWalk rootId addr bitsRemaining st = none := by
  unfold declaredLockSetForCSpaceWalk
  simp only [Nat.not_le.mpr h, if_false]

/-- **WS-RR RR7.41**: every CNode on the walk's path has its read lock declared
— the coverage half, and the one a false footprint would fail. -/
theorem mem_cspaceWalkLockSet_cnode (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr)
    (bitsRemaining : Nat) (st : SystemState) (oid : SeLe4n.ObjId)
    (h : oid ∈ cspaceWalkPath rootId addr bitsRemaining st)
    (hCn : (st.getCNode? oid).isSome) :
    ∃ m, (cnodeLock oid, m) ∈ (cspaceWalkLockSet rootId addr bitsRemaining st).pairs := by
  unfold cspaceWalkLockSet
  refine Concurrency.lockSetOfList_mem_of_mem _ (cnodeLock oid) AccessMode.read
    (List.mem_map.mpr ⟨oid, h, ?_⟩)
  unfold cspaceWalkKeyLock
  cases hc : st.getCNode? oid with
  | none => rw [hc] at hCn; cases hCn
  | some _ => rfl

/-- **PR #892 review round 4**: a key on the path that holds no CNode declares
the state-level read lock — the member that conflicts with every structural
writer, so a failed lookup is a read the footprint names. -/
theorem mem_cspaceWalkLockSet_missing (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr)
    (bitsRemaining : Nat) (st : SystemState) (oid : SeLe4n.ObjId)
    (h : oid ∈ cspaceWalkPath rootId addr bitsRemaining st)
    (hNone : st.getCNode? oid = none) :
    ∃ m, (Concurrency.stateLevelLock, m)
      ∈ (cspaceWalkLockSet rootId addr bitsRemaining st).pairs := by
  unfold cspaceWalkLockSet
  refine Concurrency.lockSetOfList_mem_of_mem _ Concurrency.stateLevelLock AccessMode.read
    (List.mem_map.mpr ⟨oid, h, ?_⟩)
  unfold cspaceWalkKeyLock
  rw [hNone]

-- ============================================================================
-- §3  The conflict a delete now has
-- ============================================================================

/-- **WS-RR RR7.41 (the payoff)**: a `cspaceDelete` whose target CNode lies on a
resolution's path **conflicts** with that resolution.

The delete declares `cnodeLock targetCnodeObjId` in **write** mode
(`lockSet_cspaceDelete`); the resolution now declares the same key in **read**
mode; and `AccessMode.conflicts` holds of a read/write pair.  So the SM3.E
serializability machinery orders the two rather than letting them interleave —
which is exactly what a resolution passing through a slot being deleted needs,
and exactly what could not be said while the footprint named only the root.

Stated against `ktiSharesConflictingLock`, the relation SM3.E's conflict order is
built from, so the result is consumed by the existing argument rather than being
a fresh claim beside it. -/
theorem cspaceWalk_conflicts_with_delete (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr)
    (bitsRemaining : Nat) (st : SystemState)
    (callerTid : SeLe4n.ThreadId) (deleteRoot targetCnode : SeLe4n.ObjId)
    (hOnPath : targetCnode ∈ cspaceWalkPath rootId addr bitsRemaining st) :
    ∃ (l : LockId) (m₁ m₂ : AccessMode),
      (l, m₁) ∈ (cspaceWalkLockSet rootId addr bitsRemaining st).pairs ∧
      (l, m₂) ∈ (Concurrency.lockSet_cspaceDelete callerTid deleteRoot targetCnode).pairs ∧
      AccessMode.conflicts m₁ m₂ = true := by
  -- PR #892 review round 4: on **both** arms.  A target the walk read as a
  -- CNode conflicts on that CNode's lock; a target the walk read and found no
  -- CNode at conflicts on the state-level lock the delete also declares.
  cases hCn : st.getCNode? targetCnode with
  | some _ =>
      obtain ⟨m, hm⟩ := mem_cspaceWalkLockSet_cnode rootId addr bitsRemaining st targetCnode
        hOnPath (by rw [hCn]; rfl)
      refine ⟨cnodeLock targetCnode, m, AccessMode.write, hm, ?_, ?_⟩
      · exact Concurrency.lockSet_cspaceDelete_target_write_mem callerTid deleteRoot targetCnode
      · cases m <;> rfl
  | none =>
      obtain ⟨m, hm⟩ := mem_cspaceWalkLockSet_missing rootId addr bitsRemaining st targetCnode
        hOnPath hCn
      refine ⟨Concurrency.stateLevelLock, m, AccessMode.write, hm, ?_, ?_⟩
      · exact Concurrency.lockSet_cspaceDelete_stateLevel_write_mem callerTid deleteRoot
          targetCnode
      · cases m <;> rfl

-- ============================================================================
-- §3b  A single-level resolution reads only its root
-- ============================================================================

/-- **WS-RR RR7.41**: a resolution whose root consumes every address bit reads
**exactly** that root.

This is the fact the existing root-only footprints rest on, and until now it was
argued rather than proved.  RR7.12's `abiEntryGate` refuses a resolution unless
`rootCn.depth = rootCn.guardWidth + rootCn.radixWidth` — the root consumes all
the bits, so `resolveCapAddress` reaches its leaf arm on the first hop and never
descends.  Under that condition `cspaceWalkPath` is `[rootId]`, so
`cnodeLock cnodeRootObjId` **is** the complete CNode footprint of every
resolution the live seam declares one for.

That closes the interior question at the live seam rather than deferring it: a
declared footprint covers the whole walk because the walk is one hop, and a
multi-level walk — which `abiEntryGate` refuses, so no footprint is declared for
it — has `cspaceWalkLockSet` if a future consumer wants to admit one.  The
mechanism and the reason it is not yet needed are both stated, which is what
"the domain is covered" has to mean. -/
theorem cspaceWalkPath_single_level (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr)
    (st : SystemState) (cn : CNode)
    (hRoot : st.getCNode? rootId = some cn)
    (hDepth : cn.depth = cn.guardWidth + cn.radixWidth)
    (hPos : cn.depth ≠ 0) :
    cspaceWalkPath rootId addr cn.depth st = [rootId] := by
  unfold cspaceWalkPath
  rw [dif_neg hPos, hRoot]
  simp only
  by_cases hCons : cn.guardWidth + cn.radixWidth = 0
  · rw [dif_pos hCons]
  · rw [dif_neg hCons]
    -- the root consumes every bit, so neither the short-bit arm nor the descent
    -- arm can fire
    rw [if_neg (by rw [hDepth]; exact Nat.lt_irrefl _)]
    split
    · rfl
    · rw [if_pos (by rw [hDepth]; exact Nat.sub_self _)]

/-- **WS-RR RR7.41**: the single-level footprint is exactly the root's read lock
— so a root-only declaration is *complete*, not an approximation, for every
resolution the live ABI seam admits. -/
theorem cspaceWalkLockSet_single_level (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr)
    (st : SystemState) (cn : CNode)
    (hRoot : st.getCNode? rootId = some cn)
    (hDepth : cn.depth = cn.guardWidth + cn.radixWidth)
    (hPos : cn.depth ≠ 0) :
    (cspaceWalkLockSet rootId addr cn.depth st).pairs
      = [(cnodeLock rootId, AccessMode.read)] := by
  unfold cspaceWalkLockSet
  rw [cspaceWalkPath_single_level rootId addr st cn hRoot hDepth hPos]
  simp only [List.map, cspaceWalkKeyLock, hRoot]
  rfl

/-- **PR #892 review round 4**: and it is within the ceiling, so the live seam's
single-level resolution is always *declared* — the refusal above touches only
walks deeper than the ladder can carry. -/
theorem declaredLockSetForCSpaceWalk_single_level (rootId : SeLe4n.ObjId)
    (addr : SeLe4n.CPtr) (st : SystemState) (cn : CNode)
    (hRoot : st.getCNode? rootId = some cn)
    (hDepth : cn.depth = cn.guardWidth + cn.radixWidth)
    (hPos : cn.depth ≠ 0) :
    declaredLockSetForCSpaceWalk rootId addr cn.depth st
      = some (cspaceWalkLockSet rootId addr cn.depth st) := by
  apply declaredLockSetForCSpaceWalk_of_le
  unfold LockSet.size
  rw [cspaceWalkLockSet_single_level rootId addr st cn hRoot hDepth hPos,
    List.length_singleton]
  decide

-- ============================================================================
-- §4  The bracket
-- ============================================================================

/-- **WS-RR RR7.41**: run a multi-level resolution inside the footprint its own
walk declares.

`runUnderDeclaredLockSet` — RR7.12's bracket, unchanged — at a `declared` that
walks rather than reads an argument.  The revalidation is doing real work here,
unlike at the per-core scheduler entries: the path is resolved by reads taken
*before* the interior locks are held, so another core can redirect it in between,
and the guard refuses exactly that.  A refusal commits nothing but the unwinding
(`runUnderDeclaredLockSet_refused`).

This is the mechanism a CPtr-resolving footprint adopts to cover its interior; it
is not yet what `lockSetForSyscall`'s arms run, which still name the root alone
and whose ABI seam refuses a multi-level walk outright. -/
def resolveCapAddressUnderWalkLocks (lockCore : CoreId) (rootId : SeLe4n.ObjId)
    (addr : SeLe4n.CPtr) (bitsRemaining : Nat) (st : SystemState) :
    Concurrency.LockBracketOutcome (Except KernelError SlotRef) :=
  runUnderDeclaredLockSet (declaredLockSetForCSpaceWalk rootId addr bitsRemaining) lockCore
    (fun s => (resolveCapAddress rootId addr bitsRemaining s, s)) st

/-- **WS-RR RR7.41**: on the committed arm the bracket returns exactly the
resolution `resolveCapAddress` computes on the acquired state — bracketing
changes which locks are held, never what the walk resolves to. -/
theorem resolveCapAddressUnderWalkLocks_committed (lockCore : CoreId)
    (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (bitsRemaining : Nat)
    (st : SystemState) (S : LockSet)
    (hDecl : declaredLockSetForCSpaceWalk rootId addr bitsRemaining st = some S)
    (hGuard : declaredLockSetForCSpaceWalk rootId addr bitsRemaining
        (Concurrency.acquireAll lockCore S.lockAcquireSequence st) = some S ∧
      Concurrency.lockSetHeld lockCore S
        (Concurrency.acquireAll lockCore S.lockAcquireSequence st)) :
    resolveCapAddressUnderWalkLocks lockCore rootId addr bitsRemaining st
      = .committed
          (resolveCapAddress rootId addr bitsRemaining
             (Concurrency.acquireAll lockCore S.lockAcquireSequence st),
           Concurrency.unwindAll lockCore S.lockAcquireSequence.reverse
             (Concurrency.acquireAll lockCore S.lockAcquireSequence st)) :=
  runUnderDeclaredLockSet_committed _ lockCore _ st S hDecl hGuard

/-- **WS-RR RR7.41 (the guard has content here)**: the bracket refuses when the
walk resolved a different path under its own locks than it did before them.

At the per-core scheduler entries the revalidation is vacuous by construction
(the footprint is a function of the core id).  Here it is the substance: the
interior CNodes are discovered by reads the interior locks do not yet protect, so
a concurrent `cspaceDelete` between the walk and the acquire moves the path, and
this is the arm that catches it.  A refusal commits nothing but the unwinding. -/
theorem resolveCapAddressUnderWalkLocks_refused (lockCore : CoreId)
    (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (bitsRemaining : Nat)
    (st : SystemState) (S : LockSet)
    (hDecl : declaredLockSetForCSpaceWalk rootId addr bitsRemaining st = some S)
    (hGuard : ¬ (declaredLockSetForCSpaceWalk rootId addr bitsRemaining
        (Concurrency.acquireAll lockCore S.lockAcquireSequence st) = some S ∧
      Concurrency.lockSetHeld lockCore S
        (Concurrency.acquireAll lockCore S.lockAcquireSequence st))) :
    resolveCapAddressUnderWalkLocks lockCore rootId addr bitsRemaining st
      = .refused (Concurrency.unwindAll lockCore S.lockAcquireSequence.reverse
          (Concurrency.acquireAll lockCore S.lockAcquireSequence st)) :=
  runUnderDeclaredLockSet_refused _ lockCore _ st S hDecl hGuard

end SeLe4n.Kernel
