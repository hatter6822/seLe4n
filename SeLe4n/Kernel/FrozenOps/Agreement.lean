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
  | .cnode a,        .cnode b        =>
      a.depth == b.depth && a.guardWidth == b.guardWidth
        && a.guardValue == b.guardValue && a.radixWidth == b.radixWidth
        && frozenCNodeSlotsAgree a b
  | .vspaceRoot a,   .vspaceRoot b   =>
      a.asid == b.asid && frozenVSpaceMappingsAgree a b
  | _, _ => false

/-- State-level agreement over everything both phases model.

The object store is compared over the live index **and** the frozen index, so an
object appearing on one side only is a disagreement.  The taint table is
compared at every key either side holds — the frozen operations write it, and
three of the five recorded divergences were provenance recorded against the
wrong carrier, which no object comparison can see. -/
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
  -- scheduler's current thread from the boot core; comparing against any other
  -- core would be comparing against something the frozen side never modelled.
  objectsAgree && taintAgree
    && fs.scheduler.current == ls.scheduler.currentOnCore Concurrency.bootCoreId

/-- Run-level agreement: the same refusal, or two successes whose states agree.

The refusal half is load-bearing.  A frozen operation that accepts what the live
one refuses is a divergence the state comparison never sees, because there is no
live state to compare against — and a frozen guard that went missing is exactly
how a parked sender with no message reached the frozen dequeue. -/
def frozenRunAgrees {α β : Type}
    (fr : Except KernelError (α × FrozenSystemState))
    (lr : Except KernelError (β × SystemState)) : Bool :=
  match fr, lr with
  | .error e, .error e' => e == e'
  | .ok (_, fs), .ok (_, ls) => frozenStateAgrees fs ls
  | _, _ => false

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

/-- WS-SM: the syscalls whose frozen operation is run against its live
counterpart by `FrozenOpsSuite`'s differential scenarios. -/
def frozenOpDifferentiallyChecked : SyscallId → Bool
  | .notificationSignal => true  -- against `notificationSignalBound`
  | .notificationWait => true    -- against `notificationWait`
  | .send => true                -- against `endpointSendDual`
  | .receive => true             -- against `endpointReceiveDual`
  | .call => true                -- against `endpointCall`
  | .reply => true               -- against `endpointReply`
  | _ => false

/-- WS-SM: why a frozen-covered syscall is not yet run beside its live
counterpart.  Non-empty exactly for the covered-but-unchecked ones, so the
interlock below cannot be satisfied by leaving a row blank. -/
def frozenOpUncheckedReason : SyscallId → String
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
