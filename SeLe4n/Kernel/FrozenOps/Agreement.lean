-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.FrozenOps.Operations
import SeLe4n.Kernel.API
import SeLe4n.Model.FrozenState

/-!
# Frozen/live agreement — the correspondence, as something that runs

Each frozen operation re-implements a live transition against the frozen
representation.  Which live transition it re-implements was recorded only in a
markdown table in `FrozenOps/Operations.lean`'s module docstring, and in a
`mirrors X` sentence on each operation.  Nothing ran either one.  A frozen
operation could therefore drift from the transition it claims to mirror and stay
green: the frozen suite exercised the frozen operation alone, asserting against
what a human had read in the live code and written down.

That is not a hypothetical failure mode.  It is the one that actually happened,
five separate times, each found by a reader rather than by the build — a frozen
signal that left a bound thread blocked while the live one delivered to it, a
frozen dequeue that recorded a predecessor the live one did not, a frozen waiter
whose badge vanished.  And the table is *itself* wrong: row 5 names
`notificationSignal` as `frozenNotificationSignal`'s counterpart, while the
frozen operation mirrors the bound-aware composition the live `.notificationSignal`
arm actually runs.  Reading the table is how you get the wrong answer.

This module is the correspondence expressed as a computation.  Run the live
transition on a `SystemState`, run the frozen one on that state's `freeze`, and
compare.  A divergence then fails a test instead of waiting for a reviewer, and
naming the wrong counterpart fails too — because the comparison is against the
transition you actually called.

## What "agree" means

`FrozenKernelObject` re-represents exactly two variants: `.cnode` (slots become
a `CNodeRadix`) and `.vspaceRoot` (mappings become a `FrozenMap`).  The other six
reuse the runtime types verbatim, so agreement on them is *equality*, with no
observation to choose and therefore no field anyone can forget to include.  The
two re-represented variants are compared through their lookups, in both
directions, so neither a missing entry nor an invented one passes.
-/

namespace SeLe4n.Kernel.FrozenOps

open SeLe4n.Model
open SeLe4n.Kernel.RadixTree

/-- Slot-level agreement for the one variant whose slots change representation.

Compared in **both** directions: every live slot must be present and equal in
the frozen tree, and every frozen slot must be present and equal in the live
map.  One direction alone would accept a frozen CNode carrying a capability the
live one does not. -/
def frozenCNodeSlotsAgree (f : FrozenCNode) (l : CNode) : Bool :=
  l.slots.toList.all (fun kv => f.slots.lookup kv.1 == some kv.2)
    && f.slots.toList.all (fun kv => l.slots.get? kv.1 == some kv.2)

/-- Mapping-level agreement for the other re-represented variant, in both
directions for the same reason. -/
def frozenVSpaceMappingsAgree (f : FrozenVSpaceRoot) (l : VSpaceRoot) : Bool :=
  l.mappings.toList.all (fun kv => f.mappings.get? kv.1 == some kv.2)
    && f.mappings.indexMap.toList.all (fun kv =>
         f.mappings.get? kv.1 == l.mappings.get? kv.1)

/-- Object-level agreement.  Equality on the six verbatim variants; lookup
agreement on the two re-represented ones; a kind mismatch is a disagreement. -/
def frozenObjectAgrees (f : FrozenKernelObject) (l : KernelObject) : Bool :=
  match f, l with
  | .tcb a,          .tcb b          => a == b
  | .endpoint a,     .endpoint b     => a == b
  | .notification a, .notification b => a == b
  | .untyped a,      .untyped b      => a == b
  | .schedContext a, .schedContext b => a == b
  | .reply a,        .reply b        => a == b
  -- PR #873 round 16: the two re-represented variants are **destructured**, not
  -- sampled.  Listing the fields to compare is how `lock` came to be omitted --
  -- both frozen structures carry it precisely so freezing preserves it, so a
  -- frozen operation acquiring or releasing one differently from its live
  -- counterpart passed.  A binding here that goes unused is a field nobody
  -- compared, which the unused-variable linter reports; adding a field to
  -- either structure breaks this pattern until someone decides about it.
  | .cnode (fc@⟨fd, fgw, fgv, frw, _fslots, flock⟩),
    .cnode (lc@⟨ld, lgw, lgv, lrw, _lslots, llock⟩) =>
      fd == ld && fgw == lgw && fgv == lgv && frw == lrw && flock == llock
        && frozenCNodeSlotsAgree fc lc
  | .vspaceRoot (fv@⟨fasid, _fm, flock⟩), .vspaceRoot (lv@⟨lasid, _lm, llock⟩) =>
      fasid == lasid && flock == llock && frozenVSpaceMappingsAgree fv lv
  | _, _ => false

/-- State-level agreement over everything both phases model.

The object store is compared over the live index **and** the frozen index, so an
object appearing on one side only is a disagreement.  The taint table is
compared at every key either side holds — the frozen operations write it, and
three of the five recorded divergences were provenance recorded against the
wrong carrier, which no object comparison can see.  The **run queue** is
compared in both directions and by priority, because whether a woken thread can
be selected is not visible in its TCB. -/
def frozenStateAgrees (fs : FrozenSystemState) (ls : SystemState) : Bool :=
  let objectsAgree :=
    ls.objectIndex.all (fun oid =>
      match fs.objects.get? oid, ls.getObject? oid with
      | some f, some l => frozenObjectAgrees f l
      | none,   none   => true
      | _, _           => false)
    && fs.objects.indexMap.toList.all (fun kv =>
         match fs.objects.get? kv.1, ls.getObject? kv.1 with
         | some f, some l => frozenObjectAgrees f l
         | none,   none   => true
         | _, _           => false)
  let taintKeys :=
    (show List (SeLe4n.ObjId × SeLe4n.Kernel.DeclassificationTaint)
       from fs.declassificationTaint.entries).map Prod.fst
      ++ (show List (SeLe4n.ObjId × SeLe4n.Kernel.DeclassificationTaint)
            from ls.declassificationTaint.entries).map Prod.fst
  let taintAgree :=
    taintKeys.all (fun oid =>
      fs.declassificationTaint oid == ls.declassificationTaint oid)
  -- The frozen phase is single-core by construction, and `freeze` takes the
  -- scheduler's state from the boot core; comparing against any other core would
  -- be comparing against something the frozen side never modelled.
  --
  -- PR #873 round 15: **the whole run queue, not just the current thread.**
  -- Comparing `current` alone accepted states whose run queues differ, which is
  -- the difference between a thread the scheduler can select and one it cannot.
  -- It is the divergence a wake produces, so leaving it out made the wake paths
  -- -- the very paths the recorded divergences were on -- the ones this relation
  -- could not see.
  --
  -- The subject is `byPriority`, because that is what *selection* reads:
  -- `frozenChooseThread` folds over its buckets and the live `chooseThread` over
  -- the same field, so two states whose buckets agree can select the same
  -- threads.  `membership` is deliberately not compared -- a `FrozenSet` is a
  -- key-presence map with `Unit` values, so frozen membership cannot change at
  -- all, and `frozenSchedule`'s own docstring records it as a read-only record
  -- of the population at freeze time.  Requiring it to track the live run queue
  -- would be requiring the representation to be something it is not; requiring
  -- the buckets to track it is requiring the frozen kernel to schedule the same
  -- threads, which is the claim that matters.
  let lq := ls.scheduler.runQueueOnCore Concurrency.bootCoreId
  let queueAgree :=
    -- Both directions over the union of bucket keys: a thread queued on one side
    -- only is a disagreement whichever side queues it, and an empty bucket on
    -- one side must face an empty or absent bucket on the other.
    (lq.byPriority.toList.map Prod.fst
        ++ fs.scheduler.byPriority.indexMap.toList.map Prod.fst).all (fun prio =>
      (fs.scheduler.byPriority.get? prio).getD [] == (lq.byPriority[prio]?).getD [])
  objectsAgree && taintAgree && queueAgree
    && fs.scheduler.current == ls.scheduler.currentOnCore Concurrency.bootCoreId
    && fs.scheduler.activeDomain == ls.scheduler.activeDomainOnCore Concurrency.bootCoreId

/-- Run-level agreement: the same refusal, or two successes whose states agree.

The refusal half is load-bearing.  A frozen operation that accepts what the live
one refuses is a divergence the state comparison never sees, because there is no
live state to compare against — and a frozen guard that went missing is exactly
how a parked sender with no message reached the frozen dequeue. -/
def frozenRunAgrees {α β : Type}
    (resultAgrees : α → β → Bool)
    (fr : Except KernelError (α × FrozenSystemState))
    (lr : Except KernelError (β × SystemState)) : Bool :=
  match fr, lr with
  | .error e, .error e' => e == e'
  | .ok (fa, fs), .ok (la, ls) => resultAgrees fa la && frozenStateAgrees fs ls
  | _, _ => false

/-- The result relation for the transitions that answer `Unit`: nothing to
compare, and saying so takes an argument rather than a wildcard. -/
def unitResultAgrees : Unit → Unit → Bool := fun _ _ => true

/-! ## The obligation: claiming coverage means running both

`frozenOpCoverage` (`FrozenOps/Operations.lean`) already says, for every
`SyscallId`, whether a frozen operation exists for it — and being total over the
type, it forces a new syscall to state one way or the other.  What it cannot say
is whether the frozen operation that exists still *does what the live one does*.
It is a claim about existence, and every recorded divergence was a frozen
operation that existed.

`frozenOpDifferentiallyChecked` is the other half: the syscalls whose frozen
operation the suite runs **beside** its live counterpart, on one state, comparing
the results.  It is total over `SyscallId` for the same reason, and the two are
interlocked below, so a covered syscall must either be differentially checked or
carry a stated reason it is not.  A gap is then a row someone wrote, not a row
nobody noticed. -/

/-- **The branches a frozen IPC operation can take.**

The coverage claim was keyed by `SyscallId`, so one scenario satisfied a whole
syscall.  `.send` was claimed on a fixture with *no receiver waiting*: the
rendezvous branch — a different transition, which the live `endpointSendDual`
completes with `storeTcbReceiveComplete` — was never compared against anything,
and neither was the call rendezvous that stages a reply.  Two of the divergences
found in round 17 lived in branches a per-syscall row reported as checked.

A row per branch cannot stop someone adding a branch without listing it; the
`SyscallId` keying could not do that either.  What it does is make the unit of
the claim the unit of the transition, so a `true` means the comparison ran on the
shape being claimed rather than on whichever shape the fixture happened to hit.

The list is the discriminating test each operation actually performs —
`receiveQ.head`, `sendQ.head` plus the dequeued sender's `ipcState`,
`pendingBadge`, `boundTCB` then `waitingThreads` — not a grouping chosen for the
table. -/
inductive FrozenOpBranch where
  /-- A signal delivered straight to the notification's bound TCB. -/
  | notificationSignalToBoundThread
  /-- A signal delivered to an ordinary waiter popped from `waitingThreads`. -/
  | notificationSignalToWaiter
  /-- A signal with no waiter and no bound thread: the badge is stored. -/
  | notificationSignalStoresBadge
  /-- A wait that takes a badge already pending. -/
  | notificationWaitConsumesBadge
  /-- A wait with nothing pending: the caller blocks. -/
  | notificationWaitBlocks
  /-- A send that finds a receiver waiting. -/
  | endpointSendToWaitingReceiver
  /-- A send with no receiver: the sender parks with its message. -/
  | endpointSendParks
  /-- A receive that dequeues a `.blockedOnSend` sender. -/
  | endpointReceiveFromBlockedSender
  /-- A receive that dequeues a `.blockedOnCall` caller. -/
  | endpointReceiveFromBlockedCaller
  /-- A receive with no sender queued: the receiver blocks. -/
  | endpointReceiveBlocks
  /-- A call that finds a receiver waiting. -/
  | endpointCallToWaitingReceiver
  /-- A call with no receiver: the caller parks. -/
  | endpointCallParks
  /-- A reply delivered to a linked `.blockedOnReply` caller. -/
  | endpointReplyToBlockedCaller
  deriving DecidableEq, Repr, Inhabited

/-- Every branch, for the totality the interlocks below decide over. -/
def FrozenOpBranch.all : List FrozenOpBranch :=
  [ .notificationSignalToBoundThread, .notificationSignalToWaiter,
    .notificationSignalStoresBadge, .notificationWaitConsumesBadge,
    .notificationWaitBlocks, .endpointSendToWaitingReceiver, .endpointSendParks,
    .endpointReceiveFromBlockedSender, .endpointReceiveFromBlockedCaller,
    .endpointReceiveBlocks, .endpointCallToWaitingReceiver, .endpointCallParks,
    .endpointReplyToBlockedCaller ]

/-- The syscall each branch belongs to. -/
def FrozenOpBranch.syscall : FrozenOpBranch → SyscallId
  | .notificationSignalToBoundThread => .notificationSignal
  | .notificationSignalToWaiter => .notificationSignal
  | .notificationSignalStoresBadge => .notificationSignal
  | .notificationWaitConsumesBadge => .notificationWait
  | .notificationWaitBlocks => .notificationWait
  | .endpointSendToWaitingReceiver => .send
  | .endpointSendParks => .send
  | .endpointReceiveFromBlockedSender => .receive
  | .endpointReceiveFromBlockedCaller => .receive
  | .endpointReceiveBlocks => .receive
  | .endpointCallToWaitingReceiver => .call
  | .endpointCallParks => .call
  | .endpointReplyToBlockedCaller => .reply

/-- WS-SM: the **branches** whose frozen transition is run against its live
counterpart by `FrozenOpsSuite`'s differential scenarios. -/
def frozenBranchDifferentiallyChecked : FrozenOpBranch → Bool
  | .notificationSignalToBoundThread => true   -- against `notificationSignalBound`
  | .notificationWaitConsumesBadge => true     -- against `notificationWait`
  | .notificationWaitBlocks => true            -- against `notificationWait` (the
                                               -- idle park; pins the atomic
                                               -- `pendingMessage` clear on both
                                               -- sides -- PR #886 review)
  | .endpointSendParks => true                 -- against `endpointSendDual`
  | .endpointSendToWaitingReceiver => true     -- against `endpointSendDual`
  | .endpointReceiveFromBlockedSender => true  -- against `endpointReceiveDual`
  | .endpointReceiveFromBlockedCaller => true  -- against `endpointReceiveDual`
  | .endpointCallParks => true                 -- against `endpointCall`
  | .endpointReplyToBlockedCaller => true      -- against `endpointReply`
  | _ => false

/-- Why a branch is not yet run beside its live counterpart.  Non-empty exactly
for the unchecked ones, so the interlock cannot be satisfied by a blank row. -/
def frozenBranchUncheckedReason : FrozenOpBranch → String
  | .notificationSignalToWaiter => "ordinary-waiter delivery; scenario owed"
  | .notificationSignalStoresBadge => "store-only signal; scenario owed"
  | .endpointReceiveBlocks => "blocking receive; scenario owed"
  | .endpointCallToWaitingReceiver => "call rendezvous; scenario owed"
  | _ => ""

/-- **Every branch is either checked or carries a stated reason.**

Decided over `FrozenOpBranch.all`, so a new constructor makes this fail to
elaborate until its row exists. -/
theorem frozenBranch_checked_or_reasoned :
    FrozenOpBranch.all.all (fun b =>
      frozenBranchDifferentiallyChecked b
        || !(frozenBranchUncheckedReason b).isEmpty) = true := by
  decide

/-- A checked branch carries no "owed" reason, and an unchecked one carries no
empty reason: the two tables partition rather than overlap. -/
theorem frozenBranchUncheckedReason_only_when_unchecked :
    FrozenOpBranch.all.all (fun b =>
      frozenBranchDifferentiallyChecked b
        == (frozenBranchUncheckedReason b).isEmpty) = true := by
  decide

/-- WS-SM: a syscall is differentially checked when **every** branch of it is.

The per-syscall claim is now derived from the per-branch ones rather than
asserted beside them, so it cannot say "checked" while a branch of that syscall
has never run.  That is what it used to do: six syscalls read `true` while seven
of their thirteen branches had no comparison behind them. -/
def frozenOpDifferentiallyChecked (sid : SyscallId) : Bool :=
  -- The `any` guard is load-bearing: without it a syscall with no branches
  -- listed would satisfy the `all` vacuously and claim to be checked.
  FrozenOpBranch.all.any (fun b => b.syscall == sid)
    && FrozenOpBranch.all.all (fun b =>
         b.syscall != sid || frozenBranchDifferentiallyChecked b)

/-- WS-SM: why a frozen-covered syscall is not yet run beside its live
counterpart.  Non-empty exactly for the covered-but-unchecked ones, so the
interlock below cannot be satisfied by leaving a row blank. -/
def frozenOpUncheckedReason : SyscallId → String
  -- Partially checked: some branches run beside their live counterpart and some
  -- do not.  Named here rather than rounded up to `true`, which is what the
  -- per-syscall keying used to do -- see `frozenBranchUncheckedReason` for which.
  | .notificationSignal => "branch scenarios owed; see frozenBranchUncheckedReason"
  | .receive => "branch scenarios owed; see frozenBranchUncheckedReason"
  | .call => "branch scenarios owed; see frozenBranchUncheckedReason"
  | .cspaceMint => "capability operation; scenario owed"
  | .cspaceDelete => "capability operation; scenario owed"
  | .vspaceMap => "read-only in the frozen phase; scenario owed"
  | .vspaceUnmap => "read-only in the frozen phase; scenario owed"
  | .serviceQuery => "service lookup; scenario owed"
  | .replyRecv => "compound reply+receive; scenario owed"
  | .schedContextConfigure => "budget operation; scenario owed"
  | .schedContextBind => "budget operation; scenario owed"
  | .schedContextUnbind => "budget operation; scenario owed"
  | .tcbSetPriority => "priority operation; scenario owed"
  | .tcbSetMCPriority => "priority operation; scenario owed"
  | .tcbSetIPCBuffer => "architecture operation; scenario owed"
  -- These two are not `Kernel`-shaped on the live side: `suspendThread` and
  -- `resumeThreadOnCore` take a `ValidThreadId` and answer an `Except` over the
  -- state directly, so running them beside the frozen pair needs an adapter
  -- rather than a scenario.  Named rather than dropped.
  | .tcbSuspend => "live entry is not Kernel-shaped; adapter owed"
  | .tcbResume => "live entry is not Kernel-shaped; adapter owed"
  | _ => ""

/-- **The interlock.**  Every syscall `frozenOpCoverage` claims a frozen
operation for is either run beside its live counterpart or carries a stated
reason it is not.  Adding a frozen operation and claiming coverage for it
therefore forces a choice: write the differential scenario, or say why not.

Decided by `SyscallId`'s finiteness, so a new constructor makes this theorem
fail to elaborate until its row exists — the same forcing `frozenOpCoverage`
itself relies on. -/
theorem frozenOpCoverage_obliges_differential_check :
    SyscallId.all.all (fun sid =>
      !frozenOpCoverage sid
        || frozenOpDifferentiallyChecked sid
        || !(frozenOpUncheckedReason sid).isEmpty) = true := by
  decide

/-- **The sound direction, load-bearing the other way.**  A differential
scenario may only claim a syscall that has a frozen operation at all — otherwise
the check would be comparing the live transition against nothing. -/
theorem frozenOpDifferentiallyChecked_implies_covered :
    SyscallId.all.all (fun sid =>
      !frozenOpDifferentiallyChecked sid || frozenOpCoverage sid) = true := by
  decide

/-- **A reason is not a substitute for a check.**  No syscall may be both run
and excused: an excuse left behind after the scenario landed would quietly
re-open the interlock's escape hatch. -/
theorem frozenOpUncheckedReason_only_when_unchecked :
    SyscallId.all.all (fun sid =>
      (frozenOpUncheckedReason sid).isEmpty
        || !frozenOpDifferentiallyChecked sid) = true := by
  decide

end SeLe4n.Kernel.FrozenOps
