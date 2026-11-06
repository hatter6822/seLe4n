-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.FrozenOps.Core

/-!
# The frozen release queue (WS-ZA ZA6.37)

The frozen mirror of the release queue's link edits
(`SeLe4n/Kernel/SchedContext/ReleaseLinks.lean`).  The frozen store holds the
scheduling contexts' records verbatim, release links and all, and the frozen
scheduler holds each core's release-queue head and count
(`FrozenSchedulerState.releaseHeadCode`, `releaseCount`), copied by `freeze`.
Each edit here is the live edit's structure over the frozen store: the same
walk to the predecessor, the same splice, the same head and count writes, so a
frozen configure or budget tick leaves the links the live one leaves and the
two states compare whole (`frozenStateAgrees`).

The boot core's abstract snapshot (`FrozenSchedulerState.replenishQueue`) is
re-read along the links after each edit to that core, the derivation `freeze`
takes it from, so it has one owner: the links.
-/

namespace SeLe4n.Kernel.FrozenOps

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.ReleaseChain (code decode)
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

/-- Core `c`'s frozen release-queue head code (`0` for an empty queue). -/
@[inline] def frozenReleaseHeadOn (st : FrozenSystemState) (c : CoreId) : Nat :=
  st.scheduler.releaseHeadCode.get c

/-- How many contexts core `c`'s frozen release queue holds. -/
@[inline] def frozenReleaseCountOn (st : FrozenSystemState) (c : CoreId) : Nat :=
  st.scheduler.releaseCount.get c

/-- `s`'s successor code on core `c`'s queue (`0` off it): the live
`releaseNextOn` over the frozen store. -/
@[inline] def frozenReleaseNextOn (st : FrozenSystemState) (c : CoreId)
    (s : SeLe4n.SchedContextId) : Nat :=
  match st.getSchedContext? s with
  | some sc => if sc.releaseCoreCode = c.val + 1 then sc.releaseNextCode else 0
  | none => 0

/-- `s`'s release time on core `c`'s queue (`0` off it): the live
`releaseAtOn`. -/
@[inline] def frozenReleaseAtOn (st : FrozenSystemState) (c : CoreId)
    (s : SeLe4n.SchedContextId) : Nat :=
  match st.getSchedContext? s with
  | some sc => if sc.releaseCoreCode = c.val + 1 then sc.releaseAt else 0
  | none => 0

/-- Is `s` on core `c`'s frozen release queue?  The live `releaseQueuedOn`. -/
@[inline] def frozenReleaseQueuedOn (st : FrozenSystemState) (c : CoreId)
    (s : SeLe4n.SchedContextId) : Bool :=
  match st.getSchedContext? s with
  | some sc => sc.releaseCoreCode == c.val + 1
  | none => false

/-- The live `releaseWalk`: the contexts read from code `h` along core `c`'s
links, at most `f` of them. -/
def frozenReleaseWalk (st : FrozenSystemState) (c : CoreId) :
    Nat → Nat → List SeLe4n.SchedContextId
  | 0, _ => []
  | f + 1, h => if h = 0 then [] else decode h :: frozenReleaseWalk st c f (frozenReleaseNextOn st c (decode h))

/-- Core `c`'s frozen queue read along its links, each member with its release
time: the live `releaseEntriesOn`. -/
def frozenReleaseEntriesOn (st : FrozenSystemState) (c : CoreId) :
    List (SeLe4n.SchedContextId × Nat) :=
  (frozenReleaseWalk st c (frozenReleaseCountOn st c) (frozenReleaseHeadOn st c)).map
    fun s => (s, frozenReleaseAtOn st c s)

/-- The live `releasePredBefore`: the member after which a context released at
`t` goes (`p` for the head). -/
def frozenReleasePredBefore (st : FrozenSystemState) (c : CoreId) (t : Nat) :
    Nat → Nat → Nat → Nat
  | 0, p, _ => p
  | f + 1, p, h =>
    if h = 0 then p
    else if t < frozenReleaseAtOn st c (decode h) then p
    else frozenReleasePredBefore st c t f h (frozenReleaseNextOn st c (decode h))

/-- The live `releasePredOf`: the code of `s`'s predecessor (`p` for the head). -/
def frozenReleasePredOf (st : FrozenSystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    Nat → Nat → Nat → Nat
  | 0, p, _ => p
  | f + 1, p, h =>
    if h = 0 then p else if decode h = s then p
    else frozenReleasePredOf st c s f h (frozenReleaseNextOn st c (decode h))

/-- Rewrite context `s`'s record by `g` in its slot; a slot holding no context
is left as it is (the live `mapSchedContextInPlace`). -/
def frozenMapSchedContext (st : FrozenSystemState) (s : SeLe4n.SchedContextId)
    (g : SeLe4n.Kernel.SchedContext → SeLe4n.Kernel.SchedContext) : FrozenSystemState :=
  match st.getSchedContext? s with
  | some sc => frozenRewriteObject st s.toObjId (.schedContext (g sc))
  | none => st

/-- Write core `c`'s head and count. -/
@[inline] def frozenSetReleaseEnds (st : FrozenSystemState) (c : CoreId) (head count : Nat) :
    FrozenSystemState :=
  { st with scheduler := { st.scheduler with
      releaseHeadCode := st.scheduler.releaseHeadCode.set c.val head c.isLt
      releaseCount := st.scheduler.releaseCount.set c.val count c.isLt } }

/-- Re-read the boot core's abstract snapshot along its links, as `freeze`
does, after an edit to core `c`'s queue. -/
def frozenReleaseResnapshot (st : FrozenSystemState) (c : CoreId) : FrozenSystemState :=
  if c = bootCoreId then
    let es := frozenReleaseEntriesOn st bootCoreId
    { st with scheduler := { st.scheduler with
        replenishQueue := { entries := es, size := es.length } } }
  else st

/-- The live `releaseUnlinkOn` over the frozen store: `s`'s predecessor (or the
head) takes over its successor, `s` is marked on no core, and the count drops.
A context not on `c`'s queue is left as it is. -/
def frozenReleaseUnlinkOn (st : FrozenSystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    FrozenSystemState :=
  if frozenReleaseQueuedOn st c s then
    let count := frozenReleaseCountOn st c
    let head := frozenReleaseHeadOn st c
    let p := frozenReleasePredOf st c s count 0 head
    let n := frozenReleaseNextOn st c s
    let st1 := frozenMapSchedContext st s SeLe4n.Kernel.SchedContext.leaveRelease
    let st2 := if p = 0 then st1
      else frozenMapSchedContext st1 (decode p) (SeLe4n.Kernel.SchedContext.withReleaseNext n)
    frozenSetReleaseEnds st2 c (if p = 0 then n else head) (count - 1)
  else st

/-- The live `releaseLinkIn`: `s`, released at `t`, linked into core `c`'s
queue after every member released no later than `t`, and counted. -/
def frozenReleaseLinkIn (st : FrozenSystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) : FrozenSystemState :=
  let head := frozenReleaseHeadOn st c
  let count := frozenReleaseCountOn st c
  let p := frozenReleasePredBefore st c t count 0 head
  let n := if p = 0 then head else frozenReleaseNextOn st c (decode p)
  let st1 := frozenMapSchedContext st s (SeLe4n.Kernel.SchedContext.joinRelease c n t)
  let st2 := if p = 0 then st1
    else frozenMapSchedContext st1 (decode p) (SeLe4n.Kernel.SchedContext.withReleaseNext (code s))
  frozenSetReleaseEnds st2 c (if p = 0 then code s else head) (count + 1)

/-- The live `releaseRemoveOn`: `s` unlinked from core `c`'s queue. -/
def frozenReleaseRemoveOn (st : FrozenSystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    FrozenSystemState :=
  frozenReleaseResnapshot (frozenReleaseUnlinkOn st c s) c

/-- The core whose queue `s`'s own link names, if any: the live
`releaseCoreOf`. -/
@[inline] def frozenReleaseCoreOf (st : FrozenSystemState) (s : SeLe4n.SchedContextId) :
    Option CoreId :=
  (st.getSchedContext? s).bind SeLe4n.Kernel.SchedContext.releaseCore?

/-- The live `releaseQueuedAnywhere`: does `s`'s link name a core? -/
@[inline] def frozenReleaseQueuedAnywhere (st : FrozenSystemState) (s : SeLe4n.SchedContextId) :
    Bool :=
  match st.getSchedContext? s with
  | some sc => sc.releaseCoreCode != 0 && decide (sc.releaseCoreCode ≤ SeLe4n.Kernel.Concurrency.numCores)
  | none => false

/-- The live `releaseInsertOn`: a context on no queue linked in at `t`; a
queued context, or no context, left as it is. -/
def frozenReleaseInsertOn (st : FrozenSystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) : FrozenSystemState :=
  if frozenReleaseQueuedAnywhere st s || (st.getSchedContext? s).isNone then st
  else frozenReleaseResnapshot (frozenReleaseLinkIn st c s t) c

/-- **The frozen mirror of `purgeReplenishment`** (the live
`releaseRemoveAnywhere`): `s` off the queue its own link names, whichever core
that is. -/
def frozenPurgeReplenishment (st : FrozenSystemState) (s : SeLe4n.SchedContextId) :
    FrozenSystemState :=
  match frozenReleaseCoreOf st s with
  | some d => frozenReleaseRemoveOn st d s
  | none => st

/-- The live `releaseFreeFor`: `s`'s link names `c`, or no core. -/
@[inline] def frozenReleaseFreeFor (st : FrozenSystemState) (c : CoreId)
    (s : SeLe4n.SchedContextId) : Bool :=
  match frozenReleaseCoreOf st s with
  | some d => d == c
  | none => true

/-- **The frozen mirror of `releasePlace`**: `s` off core `c`'s queue, then
linked in at its place (`releaseKey?`) when it has one.  A context linked on
another core's queue is left as it is. -/
def frozenReleasePlace (st : FrozenSystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    FrozenSystemState :=
  if frozenReleaseFreeFor st c s then
    match (st.getSchedContext? s).bind SeLe4n.Kernel.SchedContext.releaseKey? with
    | some t => frozenReleaseInsertOn (frozenReleaseRemoveOn st c s) c s t
    | none => frozenReleaseRemoveOn st c s
  else st

/-- The live `determineTargetCore` over the frozen store: a thread's affinity
core, or the boot core. -/
def frozenDetermineTargetCore (st : FrozenSystemState) (tid : SeLe4n.ThreadId) : CoreId :=
  match frozenLookupTcb st tid with
  | some tcb =>
    match tcb.cpuAffinity with
    | some c' => c'
    | none => bootCoreId
  | none => bootCoreId

end SeLe4n.Kernel.FrozenOps
