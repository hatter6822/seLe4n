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

/-- **WS-RR RR7.41**: the CNodes a multi-level resolution passes through, root
first.

Derived from the **same** recursion `resolveCapAddress` runs — same guard check,
same radix split, same child selection, same `bitsRemaining` descent — because a
footprint resolved from a different walk is a footprint for a different
resolution.  Every arm on which `resolveCapAddress` gives up yields the CNodes
visited so far, which is the fail-closed direction: a refused resolution still
read the CNodes it reached, so its footprint must still name them. -/
def cspaceWalkPath (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (bitsRemaining : Nat)
    (st : SystemState) : List SeLe4n.ObjId :=
  if hZero : bitsRemaining = 0 then []
  else
    match st.getCNode? rootId with
    | none => []
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

/-- **WS-RR RR7.41**: an unresolvable root reads nothing — the `.objectNotFound`
arm. -/
theorem cspaceWalkPath_no_root (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr)
    (bitsRemaining : Nat) (st : SystemState) (h : st.getCNode? rootId = none) :
    cspaceWalkPath rootId addr bitsRemaining st = [] := by
  unfold cspaceWalkPath
  by_cases hZero : bitsRemaining = 0
  · rw [dif_pos hZero]
  · rw [dif_neg hZero, h]

-- ============================================================================
-- §2  The footprint
-- ============================================================================

/-- **WS-RR RR7.41**: the footprint a multi-level resolution declares — a
**read** lock on every CNode it passes through.

`lockSetOfList` merges duplicate keys, so a walk that revisits a CNode (which the
capability graph permits) names it once, and `LockSet.lockAcquireSequence` sorts
the result into the SM0.I ladder order the bracket acquires in.  The walk's own
order is the CSpace's, which is not the ladder's — sorting is what lets the
existing deadlock-freedom argument carry, and is why this is a revalidating
bracket rather than a coupling walk. -/
def cspaceWalkLockSet (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (bitsRemaining : Nat)
    (st : SystemState) : LockSet :=
  lockSetOfList ((cspaceWalkPath rootId addr bitsRemaining st).map
    (fun oid => (cnodeLock oid, AccessMode.read)))

/-- **WS-RR RR7.41**: the resolution's declared footprint, in the shape the
bracket takes.

Total — every walk declares one, including the empty walk, whose footprint is
empty and whose bracket therefore acquires nothing.  There is no `none` arm
because there is no resolution whose interior cannot be named: that was the
*previous* state of affairs. -/
def declaredLockSetForCSpaceWalk (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr)
    (bitsRemaining : Nat) : SystemState → Option LockSet :=
  fun st => some (cspaceWalkLockSet rootId addr bitsRemaining st)

/-- **WS-RR RR7.41**: every CNode on the walk's path has its read lock declared
— the coverage half, and the one a false footprint would fail. -/
theorem mem_cspaceWalkLockSet (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr)
    (bitsRemaining : Nat) (st : SystemState) (oid : SeLe4n.ObjId)
    (h : oid ∈ cspaceWalkPath rootId addr bitsRemaining st) :
    ∃ m, (cnodeLock oid, m) ∈ (cspaceWalkLockSet rootId addr bitsRemaining st).pairs := by
  unfold cspaceWalkLockSet
  exact Concurrency.lockSetOfList_mem_of_mem _ (cnodeLock oid) AccessMode.read
    (List.mem_map.mpr ⟨oid, h, rfl⟩)

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
  obtain ⟨m, hm⟩ := mem_cspaceWalkLockSet rootId addr bitsRemaining st targetCnode hOnPath
  refine ⟨cnodeLock targetCnode, m, AccessMode.write, hm, ?_, ?_⟩
  · exact Concurrency.lockSet_cspaceDelete_target_write_mem callerTid deleteRoot targetCnode
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
  rfl

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
