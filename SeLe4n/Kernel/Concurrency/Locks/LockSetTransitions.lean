-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Kernel.Concurrency.Locks.Kind
import SeLe4n.Kernel.Concurrency.Locks.LockSet
import SeLe4n.Kernel.Concurrency.Locks.LockIdProjection

/-!
# WS-SM SM3.B.3 / B.4 — Per-transition `lockSet` declarations + `lockSet_consistent`

For each of seLe4n's 25 kernel syscall transitions (mirroring the
`SyscallId` enumeration in `Model/Object/Types.lean`), this module
declares the static `LockSet` describing the upper-bound footprint
of the transition's per-object lock acquisitions.

The `lockSet` declarations are **pure functions of the
post-cap-resolution arguments**: they take resolved `ObjId`s
(post-CSpace-lookup) plus the caller's `ThreadId`, and return a
`LockSet` declaring which (kind, ObjId, mode) tuples the transition
acquires.

Per plan §4.1, lockSet is the *union over all paths* — a transition
that may or may not touch an object (e.g., a receiver TCB that only
matters if a thread is blocked on the endpoint) declares the
upper-bound, conservatively over-locking but never under-locking.
Optional ObjIds enter via `Option ObjId` parameters: `none` means
the transition does NOT touch that object; `some oid` adds the
corresponding LockId to the set.

The `lockSet_consistent` theorem (SM3.B.4) is the structural
invariant: for every declared `(LockId, AccessMode)` in any
`lockSet_<τ>`, the `LockId.kind` is in the transition's permitted
set of kinds.

## Design choice: post-resolution args

The plan's pseudocode for `lockSet_endpointCall` uses raw `CPtr`s.
We use resolved `ObjId`s for two reasons:

1. **Static-ness**: a `lockSet` taking `CPtr`s would implicitly
   depend on the CSpace state (which the CPtr resolves through).
   The plan §4.1 requires lockSet to be a pure function of `(τ,
   args)` — no state.  Taking resolved ObjIds matches this.
2. **2PL ordering**: by the time SM3.C's `withLockSet` calls a
   transition, the caller has already done the cap-lookup
   (protected by the ObjStore lock at level 0 and the CNode locks
   at level 2).  The post-resolution args are the natural
   acquisition-time view.

For SM3.C's `withLockSet` to thread these properly, the caller
will perform the cap lookup (read the ObjStore and CNode in read
mode), then call `lockSet_<τ>` with the resolved ObjIds to compute
the per-object lock-set, then `withLockSet` to acquire.

## Naming convention

`lockSet_<syscallName>` where `<syscallName>` matches the
`SyscallId` variant (camelCase).  The argument order is:

  callerTid : ThreadId    -- the calling thread (always present)
  <required ObjIds>       -- transition-specific resolved ObjIds
  <optional ObjIds>       -- Option ObjId for path-dependent locks

ObjStore is **NOT** declared in per-transition lockSets — every
transition implicitly holds the ObjStore lock (in read mode for
most paths, write mode for those that insert/erase entries).
SM3.C will add the ObjStore lock as a wrapper at acquisition time.

## Audit-pass-3 (FIX): donation-path locks added per plan §4.1

Audit-pass-2 documented (rather than implemented) that 4
syscalls may traverse a SchedContext-donation path beyond their
directly-named-object footprint.  Per CLAUDE.md's
`Implement-the-improvement` rule (and plan §4.1's "lockSet is
the union over all paths" requirement), audit-pass-3 **fixes**
the gap by adding pre-resolved `Option SchedContextId` and
`Option ThreadId` arguments to the affected `lockSet_<τ>`
functions.

The 4 affected syscalls and their donation extensions:

* **`lockSet_endpointCall`** — adds `donatedScId : Option
  SchedContextId`.  When the caller has an active SC and the
  receiver is passive, `applyCallDonation` updates the SC's
  `boundThread` (write to SC).  Caller and receiver TCBs are
  already in the lockSet.

* **`lockSet_endpointReply`** — adds `donatedScId : Option
  SchedContextId`.  When the replier has a `.donated scId
  originalOwner` binding, `returnDonatedSchedContext` updates
  the SC + replier TCB + originalOwner TCB.  In the reply
  context, `originalOwner = replyTargetTid` (the original
  client), so the origin-owner TCB is already in the lockSet.
  Only the SC is a new lock.

* **`lockSet_replyRecv`** — adds `donatedScId : Option
  SchedContextId`.  Same as reply (the receive phase doesn't
  initiate donation — donation is caller-initiated via
  `endpointCall`, not receiver-initiated).

* **`lockSet_tcbSuspend`** — adds `bindingScId : Option
  SchedContextId` AND `donatedOriginalOwnerTid : Option
  ThreadId`.  `cancelDonation` dispatches:
  - `.unbound`: no extra locks.
  - `.bound scId`: writes SC + suspended TCB.  Suspended TCB
    already in lockSet; SC is new.
  - `.donated scId originalOwner`: writes SC + suspended TCB +
    originalOwner TCB.  Suspended TCB already in lockSet; SC
    and originalOwner TCB are new.

  WS-SM SM6.E additionally threads `consumedReplyId : Option
  ReplyId` (default `none`): suspending a `.blockedOnReply`
  target consumes its reply forward link (`cancelIpcBlocking` →
  `consumeReplyLink` writes `reply.caller := none`), so that
  Reply object's write lock joins the footprint.  The
  per-sub-operation footprints `lockSet_cancelIpcBlocking` /
  `lockSet_cancelDonation` (SM6.E, in
  `IPC.CrossCore.Cancellation`) are member-by-member covered by
  this suspend footprint — see the
  `lockSet_tcbSuspend_*_write_mem` family there.

The caller is expected to pre-inspect the relevant TCB (under
the ObjStore read-lock + the TCB's read-lock acquired
temporarily for the inspection — sound under non-strict 2PL)
to extract these args BEFORE computing the lockSet and
acquiring it via `withLockSet`.  This pattern keeps `lockSet`
itself a pure function of `(τ, args)` while covering all
donation paths.

### Syscalls that do NOT need donation extension

* **`lockSet_endpointSend`**: send is asynchronous, no
  donation.
* **`lockSet_endpointReceive`**: receive blocks waiting; if a
  caller arrives and donates, the donation is initiated from
  the caller's `endpointCall` syscall — handled there.
* **`lockSet_notificationSignal/Wait`**: notifications don't
  donate.
* **`lockSet_cspaceMint/Copy/Move/Delete`**: capability ops
  don't touch SCs.
* **`lockSet_lifecycleRetype`**: retype creates new objects
  (born unbound), no donation.
* **`lockSet_vspaceMap/Unmap`**: VSpace ops don't touch SCs.
* **`lockSet_serviceRegister/Revoke/Query`**: service-level
  ops don't touch SCs.
* **`lockSet_schedContextConfigure`**: only changes SC params
  + bound TCB domain; bound TCB is already in lockSet.
* **`lockSet_schedContextBind`**: requires SC to be currently
  unbound (precondition); no donation involved.
* **`lockSet_schedContextUnbind`**: unbinds the SC's bound
  thread; the bound thread is already in lockSet as
  `targetTcbTid`.
* **`lockSet_tcbResume/SetPriority/SetMCPriority/SetIPCBuffer`**:
  TCB-only config ops, no donation.

### PIP-chain TCB locks

Priority-inheritance propagation walks the blocking graph and
may touch arbitrarily-many TCBs in the chain.  This is
inherently dynamic and cannot be modelled in a static lockSet.
Plan §4.1's "deadlock-freedom requires knowing the lock-set in
advance" applies via the SM0.I lock-id total order: PIP-chain
TCBs are all at hierarchy level `.tcb` (3) and are acquired in
`ObjId.val` ascending order, preserving the lock-ladder
invariant.  SM3.C's `withLockSet` combinator will handle PIP
acquisition via a sub-call pattern (acquire-walk-extend) that
preserves 2PL.
-/

namespace SeLe4n.Kernel.Concurrency

open SeLe4n
open SeLe4n.Model

-- ============================================================================
-- SM3.B helpers — common LockId constructors
-- ============================================================================

/-- WS-SM SM3.B: build the LockId for a TCB at the given ThreadId. -/
@[inline] def tcbLock (tid : ThreadId) : LockId :=
  ⟨.tcb, tid.toObjId⟩

/-- WS-SM SM3.B: build the LockId for a CNode at the given ObjId.
The ObjId here is post-resolution (typically the caller's CSpace
root or a cap-lookup target). -/
@[inline] def cnodeLock (oid : ObjId) : LockId :=
  ⟨.cnode, oid⟩

/-- WS-SM SM3.B: build the LockId for an Endpoint at the given ObjId. -/
@[inline] def endpointLock (oid : ObjId) : LockId :=
  ⟨.endpoint, oid⟩

/-- WS-SM SM3.B: build the LockId for a Notification at the given ObjId. -/
@[inline] def notificationLock (oid : ObjId) : LockId :=
  ⟨.notification, oid⟩

/-- **WS-RR RR7.38**: the object whose wait queue a thread is linked into.

A thread blocked on an endpoint or a notification sits in that object's queue,
threaded by its own `queuePrev` / `queueNext`.  Splicing it out — which
`tcbSuspend` and the cancellation paths do — writes its *neighbours'* link
fields, TCBs the splice holds no `tcbLock` for.  Those writes are authorized by
the queue owner's write lock
(`suspendFootprint_splice_neighbors_under_endpoint_lock`); making them
*excluded* against other writers of the same TCBs requires every footprint that
can target a queued thread to declare the same lock, which is what this
resolver supplies.

A `.ready` thread owns no entry here.  It may still sit in a per-core *run*
queue, whose locks are `SchedLockId` rather than `LockId` and whose coverage is
the separately registered scheduler domain — said here because the two are easy
to conflate and only one of them is closed. -/
inductive QueueOwner where
  /-- The thread is in an endpoint's send / receive / call / reply queue. -/
  | endpoint (oid : ObjId)
  /-- The thread is in a notification's wait queue. -/
  | notification (oid : ObjId)
  deriving DecidableEq, Repr

/-- The lock a `QueueOwner` denotes. -/
@[inline] def QueueOwner.lock : QueueOwner → LockId
  | .endpoint oid => ⟨.endpoint, oid⟩
  | .notification oid => ⟨.notification, oid⟩

/-- **WS-RR RR7.38**: a queue owner's kind is one of exactly two.

This is why `QueueOwner` exists rather than a bare `Option LockId`: a `LockId`
carries an arbitrary kind, so a footprint parameterised by one could only be
admitted by a `permittedKinds` arm listing *every* kind — the `.declassify`
shape, honest there because the target really can be any object, and dishonest
here because a wait queue is owned by an endpoint or a notification and nothing
else.  With the kind fixed by construction the eleven arms below admit exactly
those two, and the fixed part of each footprint stays pinned. -/
theorem QueueOwner.lock_kind (q : QueueOwner) :
    q.lock.kind = LockKind.endpoint ∨ q.lock.kind = LockKind.notification := by
  cases q <;> simp [QueueOwner.lock]

/-- **WS-RR RR7.38**: the queue owner of a TCB, read off its `ipcState`. -/
@[inline] def queueOwnerOf? (tcb : TCB) : Option QueueOwner :=
  match tcb.ipcState with
  | .blockedOnSend ep => some (.endpoint ep)
  | .blockedOnReceive ep => some (.endpoint ep)
  | .blockedOnCall ep => some (.endpoint ep)
  | .blockedOnReply ep _ => some (.endpoint ep)
  | .blockedOnNotification n => some (.notification n)
  | .ready => none

/-- **WS-RR RR7.38**: `queueOwnerOf?` resolved through the object store.  A
thread that resolves to no TCB owns no queue membership, so `none`. -/
@[inline] def queueOwnerAt (st : SystemState) (tid : ThreadId) : Option QueueOwner :=
  (st.getTcb? tid).bind queueOwnerOf?

/-- **WS-RR RR7.38**: the optional footprint member a queue owner contributes —
its lock, in **write** mode, because the splice it protects writes the neighbour
TCBs rather than reading them. -/
@[inline] def queueOwnerMember (q : Option QueueOwner) : Option (LockId × AccessMode) :=
  q.map (fun o => (o.lock, AccessMode.write))

/-- WS-SM SM3.B: build the LockId for a SchedContext at the given
SchedContextId. -/
@[inline] def schedContextLock (scid : SchedContextId) : LockId :=
  ⟨.schedContext, scid.toObjId⟩

/-- WS-SM SM6.D: build the LockId for a first-class Reply object at the given
ReplyId.  The per-object reply lock serialises the single-use `reply.caller`
write across cores — the 2PL footprint member for `.reply` / `.replyRecv` /
`.receive` / `.call` (the syscalls that link or consume a Reply object). -/
@[inline] def replyLock (rid : ReplyId) : LockId :=
  ⟨.reply, rid.toObjId⟩

/-- WS-SM SM3.B: build the LockId for a VSpaceRoot at the given ObjId. -/
@[inline] def vspaceRootLock (oid : ObjId) : LockId :=
  ⟨.vspaceRoot, oid⟩

/-- WS-SM SM3.B: build the LockId for an Untyped object at the given
ObjId. -/
@[inline] def untypedLock (oid : ObjId) : LockId :=
  ⟨.untyped, oid⟩

/-- WS-SM SM3.A.10 / PR #870 round 7: **the SystemState-level lock**, as a
declarable footprint member.

`.objStore` is the one `LockKind` whose lock word lives on `SystemState`
itself (`objStoreLock`, hierarchy level 0) rather than on an object —
`acquireLockOnObject` and `lockHeld` dispatch on the kind and read/advance
that field directly, ignoring the `objId`
(`stateLevelLock_objId_irrelevant`).  It guards the RobinHood table's
structure and, by the SM3.A.10 convention this cut makes **structural**, the
SystemState-level auxiliary structures: the declassification audit trail and
its epoch, whose three accessors (`.declassify` append, `.auditRead` read,
`.auditDrain` read-modify-write) now declare it instead of citing the
convention in prose.  One canonical spelling, `ObjId 0`, so two footprints can
never alias the singleton under different ids. -/
@[inline] def stateLevelLock : LockId :=
  ⟨.objStore, ObjId.ofNat 0⟩


-- ============================================================================
-- SM3.B helpers — LockSet builders
-- ============================================================================

/-- WS-SM SM3.B: build a `LockSet` from a list of `(LockId, AccessMode)`
pairs by folding `insertOrMerge` over the empty set.  Duplicate
keys are merged via `AccessMode.lub` (write dominates read), so
the result is well-formed by construction. -/
def lockSetOfList (pairs : List (LockId × AccessMode)) : LockSet :=
  pairs.foldl (init := LockSet.empty)
    (fun acc p => acc.insertOrMerge p.fst p.snd)

/-- WS-SM SM3.B: extend a `LockSet` with an optional pair.  `none`
leaves it unchanged; `some (l, m)` does `insertOrMerge`. -/
def lockSetExtendOpt (S : LockSet) (p : Option (LockId × AccessMode)) :
    LockSet :=
  match p with
  | none => S
  | some (l, m) => S.insertOrMerge l m

/-- WS-SM SM6.E: write-mode membership survives an optional extension (`none`
is identity, `some` is an `insertOrMerge` — covered by
`mem_insertOrMerge_write_of_mem_write`). -/
theorem mem_write_lockSetExtendOpt (S : LockSet)
    (opt : Option (LockId × AccessMode)) (l' : LockId)
    (hMem : (l', AccessMode.write) ∈ S.pairs) :
    (l', AccessMode.write) ∈ (lockSetExtendOpt S opt).pairs := by
  cases opt with
  | none => exact hMem
  | some p => exact LockSet.mem_insertOrMerge_write_of_mem_write S p.fst p.snd l' hMem

-- ============================================================================
-- SM3.B.3 — Per-transition lockSet declarations
-- ============================================================================

/-! ## IPC syscalls (5 transitions)

The IPC paths all touch the caller's TCB (write — pending message,
queue linkage, blocked state), an endpoint (write — queue
membership), and optionally a receiver TCB (write — wake-up,
register transfer).  The CSpace lookup is wrapped by the
caller-CNode lock (read).
-/

/-- WS-SM SM3.B.3: `lockSet` for `endpointSend` (syscall `.send`).

Locks acquired:
* caller TCB (write) — sets `ThreadIpcState.blocked` or transfers
  message on rendezvous.
* caller CSpace root (read) — for cap resolution.
* endpoint (write) — enqueues caller on the endpoint's send queue
  OR pairs with a waiter (dequeue + transfer).
* receiver TCB (write, optional) — present iff the endpoint had a
  blocked receiver; the receiver's state transitions to `.ready`
  and registers are loaded.

Per plan §4.1, the receiver TCB lock is part of the lock-set's
*union over all paths*.

**WS-RR RR7.7 — the capability-transfer destination.**  A rendezvous that
carries capabilities installs them into the **receiver's** CSpace root
(`ipcTransferSingleCap` → `cspaceInsertSlot`), which the pre-RR7.7 footprint
did not name at all: the only CNode member was the *caller's*, in read mode,
and on a cross-CSpace transfer those are different objects.  Two such sends
into one receiver had provably disjoint footprints while both writing that
receiver's CSpace, which is precisely what a 2PL consumer is entitled to run
concurrently.

`destCnodeObjId` is that root, threaded as the outermost pair of optionals,
and `some` adds **two** members rather than one:

* `(cnodeLock r, .write)` — the slot insert itself.  If `r` coincides with
  the caller's root, `insertOrMerge`'s `AccessMode.lub` upgrades the existing
  read rather than adding a member, so the size bound is unchanged on that
  path.
* `(stateLevelLock, .write)` — the **CDT maps**.  A capability install
  writes `SystemState`-level derivation structure, not only the slot, and
  `stateLevelLock` is SM3.A.10's `objStore` singleton, the declared subject
  for `SystemState`-level auxiliary structures.  Without it two transfers
  into *different* CSpaces would be provably disjoint while read-modify-
  writing one derivation map — the same lost-update shape PR #870 round 7
  closed for the audit trail.

`none` is the capless shape and is definitionally the identity
(`lockSetExtendOpt _ none = _`), so every pin taken before this member
existed survives by `rfl`. -/
def lockSet_endpointSend (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (endpointObjId : ObjId)
    (receiverTid : Option ThreadId)
    (destCnodeObjId : Option ObjId := none)
    -- **WS-OD OD3.11**: the queue-structure neighbour.  A rendezvous pops the
    -- receive queue, which relinks the popped receiver's successor into the
    -- head; a block enqueues on the send queue, which relinks its old tail.
    -- Exactly one of the two, and neither was declared -- so a `.send` on one
    -- core and a `.tcbSuspend` of that neighbour on another had provably
    -- disjoint footprints while both writing it.  Defaulted, so a call site
    -- that has not been re-resolved is unchanged.
    (queueNeighbour : Option ThreadId := none) : LockSet :=
  lockSetExtendOpt
    (lockSetExtendOpt
      (lockSetExtendOpt
        (lockSetExtendOpt
          (lockSetOfList
            [(tcbLock callerTid, .write),
             (cnodeLock cnodeRootObjId, .read),
             (endpointLock endpointObjId, .write)])
          (receiverTid.map (fun rt => (tcbLock rt, .write))))
        (destCnodeObjId.map (fun r => (cnodeLock r, AccessMode.write))))
      (destCnodeObjId.map (fun _ => (stateLevelLock, AccessMode.write))))
    (queueNeighbour.map (fun q => (tcbLock q, AccessMode.write)))

/-- **WS-RR RR7.7**: the capless send is definitionally the pre-RR7.7
footprint, so every statement taken over the four-argument form survives
unchanged. -/
@[simp] theorem lockSet_endpointSend_capless (callerTid : ThreadId)
    (cnodeRootObjId endpointObjId : ObjId) (receiverTid : Option ThreadId) :
    lockSet_endpointSend callerTid cnodeRootObjId endpointObjId receiverTid none
      = lockSetExtendOpt
          (lockSetOfList
            [(tcbLock callerTid, .write),
             (cnodeLock cnodeRootObjId, .read),
             (endpointLock endpointObjId, .write)])
          (receiverTid.map (fun rt => (tcbLock rt, .write))) := rfl

/-- WS-SM SM3.B.3: `lockSet` for `endpointReceive` (syscall `.receive`).

Symmetric to `send`: caller TCB blocks/unblocks; endpoint queue
mutates; optional sender TCB completes its handshake. -/
def lockSet_endpointReceive (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (endpointObjId : ObjId)
    (senderTid : Option ThreadId)
    (replyId : Option ReplyId := none)
    (installsCaps : Bool := false)
    (donatedScId : Option SchedContextId) : LockSet :=
  -- WS-SM SM6.D: a `Call` rendezvous on receive links a server-supplied Reply
  -- object (`linkCallerReply` writes `reply.caller`) under the per-object reply
  -- write-lock — folded in as an outermost optional.  `none` ⇒ the set is
  -- definitionally the pre-SM6.D footprint (`lockSetExtendOpt S none = S`), so
  -- every existing call site is unchanged.
  -- PR #873 round 8: and a rendezvous that carries capabilities **writes** the
  -- caller's own CSpace root (`ipcTransferSingleCap` → `cspaceInsertSlot`).
  --
  -- Expressed as the member's own **mode**, not as another optional.  The
  -- receiver's CSpace root *is* `cnodeRootObjId` — the receiver is the caller of
  -- `.receive`, and the arm passes `gate.cspaceRoot` — so this is the same lock
  -- in a stronger mode, and saying it that way keeps the footprint's size and
  -- acquisition order literally unchanged.  An outer `lockSetExtendOpt` would
  -- have merged to the same set while making the crude size bound count a
  -- member that cannot exist, which is a worse statement of the same fact.
  -- `false` reduces definitionally, so every pin taken before this survives.
  --
  -- **WS-RR RR7.11 — and the CDT maps, on the receive side too.**  The install
  -- is `ipcTransferSingleCap`, the same function the send and call sides run,
  -- and it does not only write the slot: it mints a derivation node for the
  -- destination (`ensureCdtNodeForSlot`, which advances the global
  -- `cdtNextNode` counter and both keyed maps) and adds an `.ipcTransfer` edge
  -- to `cdt`.  None of that decomposes by object.  RR7.7 declared it on the
  -- two sending arms; the receiving arms install through the same call and had
  -- it on neither, so two receives on different endpoints, each dequeuing a
  -- caps-bearing sender into a different CSpace, had provably disjoint
  -- footprints while read-modify-writing one derivation map — the lost-update
  -- shape that declaration exists to exclude.
  --
  -- `stateLevelLock` is SM3.A.10's `objStore` singleton, the declared subject
  -- for `SystemState`-level auxiliary structures, and it is conditioned on the
  -- same `installsCaps` flag as the root's write upgrade because it is the same
  -- write: no install, no CDT edge.  At `false` the extension is `none` and
  -- reduces definitionally, so every pin taken before this survives.
  --
  -- **WS-OD OD3.6 — and the SchedContext the rendezvous donates.**  seL4-MCS's
  -- `receiveIPC` hands the dequeued `Call` caller's scheduling context to a
  -- passive receiver, and this arm performed no donation at all until OD3.6 --
  -- so the footprint had nothing to declare and the arm had nothing to write.
  -- Now both: `donateSchedContext`'s first store writes that context's
  -- `boundThread`, under this member's write lock, and its `scThreadIndex`
  -- maintenance takes the state-level lock below.
  --
  -- Resolved by `receiveRendezvousDonatedSc?`, over the same
  -- `receiveRendezvousSender?` the `senderTid` member and `receiveInstallsCaps`
  -- read -- one resolution of "which thread does this receive dequeue", so the
  -- three members cannot disagree about it.
  lockSetExtendOpt
    (lockSetExtendOpt
      (lockSetExtendOpt
        (lockSetExtendOpt
          (lockSetOfList
            [(tcbLock callerTid, .write),
             (cnodeLock cnodeRootObjId, if installsCaps then .write else .read),
             (endpointLock endpointObjId, .write)])
          (senderTid.map (fun st => (tcbLock st, .write))))
        (replyId.map (fun rid => (replyLock rid, .write))))
      (donatedScId.map (fun sc => (schedContextLock sc, AccessMode.write))))
    -- **WS-OD OD3.6**: the state-level member is now a disjunction, for the same
    -- reason `lockSet_replyRecv`'s is: `SystemState.scThreadIndex` is an
    -- `RHTable` whose insert may rehash, so a donation writes state no per-object
    -- lock decomposes.  Declaring it only under `installsCaps` would omit it on
    -- exactly the passive-server path this row exists to make work.
    (if installsCaps || donatedScId.isSome then
       some (stateLevelLock, AccessMode.write) else none)

/-- **WS-RR RR7.11**: a receive that installs nothing — and, since **WS-OD
OD3.6**, that donates nothing — is definitionally the pre-RR7.11 footprint, so
every statement and fixture taken over the capless shape survives unchanged.
Both hypotheses are load-bearing: either write alone makes the state-level member
live, so dropping one would make the equation false rather than merely weaker. -/
@[simp] theorem lockSet_endpointReceive_no_caps (callerTid : ThreadId)
    (cnodeRootObjId endpointObjId : ObjId) (senderTid : Option ThreadId)
    (replyId : Option ReplyId) :
    lockSet_endpointReceive callerTid cnodeRootObjId endpointObjId senderTid replyId false none
      = lockSetExtendOpt
          (lockSetExtendOpt
            (lockSetOfList
              [(tcbLock callerTid, .write),
               (cnodeLock cnodeRootObjId, AccessMode.read),
               (endpointLock endpointObjId, .write)])
            (senderTid.map (fun st => (tcbLock st, .write))))
          (replyId.map (fun rid => (replyLock rid, .write))) := rfl

/-- WS-SM SM3.B.3: `lockSet` for `endpointCall` (syscall `.call`).

A blocking RPC: caller TCB writes, endpoint writes, optional
receiver TCB writes (same shape as send + receive combined).

Audit-pass-3 (donation extension): when the caller has an active
`SchedContext` and the receiver is passive (unbound),
`applyCallDonation` rebinds the SC's `boundThread` from caller to
receiver.  The receiver's TCB binding transitions to `.donated
scId callerTid`.  The caller pre-resolves this by inspecting the
caller's own TCB:

* If `callerTcb.schedContextBinding = .bound scId`: pass
  `donatedScId := some scId`.
* If `callerTcb.schedContextBinding = .unbound` or `.donated _ _`:
  pass `donatedScId := none` (no fresh donation in this call).

The receiver's currently-unbound-vs-bound status determines
whether the actual donation runs; but the lockSet declares the
upper-bound footprint regardless, so the SC lock is included
whenever the caller HAS an active SC to potentially donate. -/
def lockSet_endpointCall (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (endpointObjId : ObjId)
    (receiverTid : Option ThreadId)
    (donatedScId : Option SchedContextId)
    (replyId : Option ReplyId := none)
    -- **WS-RR RR7.7**: the capability-transfer destination, exactly as
    -- `lockSet_endpointSend` declares it and for the same reason — the
    -- receiver's CSpace root the transfer installs into, plus the
    -- state-level lock for the CDT maps the install writes.  Folding it in
    -- here is what lets `lockSet_endpointCallWithCaps` *be* this footprint
    -- at `some` rather than a second definition that has to be kept in
    -- step with it.
    (destCnodeObjId : Option ObjId := none)
    -- **WS-OD OD3.11**: the queue-structure neighbour, declared exactly as
    -- `lockSet_endpointSend` declares it and for the same reason -- `.call`
    -- takes the identical two branches through the identical two primitives.
    (queueNeighbour : Option ThreadId := none) : LockSet :=
  let withReceiver := lockSetExtendOpt
    (lockSetOfList
      [(tcbLock callerTid, .write),
       (cnodeLock cnodeRootObjId, .read),
       (endpointLock endpointObjId, .write)])
    (receiverTid.map (fun rt => (tcbLock rt, .write)))
  let withSc := lockSetExtendOpt withReceiver
    (donatedScId.map (fun sc => (schedContextLock sc, .write)))
  -- WS-SM SM6.D: a Call that rendezvouses with a waiting server links its Reply
  -- object under the per-object reply write-lock (`none` ⇒ definitionally
  -- unchanged).
  let withReply := lockSetExtendOpt withSc
    (replyId.map (fun rid => (replyLock rid, .write)))
  -- **WS-OD OD3.5**: the state-level lock is no longer conditioned on the
  -- capability transfer alone.  A Call that donates runs `donateSchedContext`,
  -- whose final step writes `SystemState.scThreadIndex` — an `RHTable`, so an
  -- insert may rehash and back-shift the whole table, exactly as the CDT maps
  -- do.  RR7.7 declared this lock for the CDT write and the donation write went
  -- undeclared beside it.  Conditioned on the same resolver as the SchedContext
  -- member, so the two cannot disagree about whether a donation happens.
  let withState := lockSetExtendOpt
    (lockSetExtendOpt withReply
      (destCnodeObjId.map (fun r => (cnodeLock r, AccessMode.write))))
    (if destCnodeObjId.isSome || donatedScId.isSome then
       some (stateLevelLock, AccessMode.write) else none)
  lockSetExtendOpt withState
    (queueNeighbour.map (fun q => (tcbLock q, AccessMode.write)))

/-- **WS-RR RR7.7**: the capless call is definitionally the pre-RR7.7
footprint, so every statement taken over the six-argument form survives
unchanged.

**WS-OD OD3.5**: and *donation-less*, since the state-level member now also
covers the donation's `scThreadIndex` write.  A capless call that donates holds
`stateLevelLock`; naming this lemma `_capless` while it silently assumed no
donation would be the presence-check shape this project keeps finding. -/
@[simp] theorem lockSet_endpointCall_capless_donationless (callerTid : ThreadId)
    (cnodeRootObjId endpointObjId : ObjId) (receiverTid : Option ThreadId)
    (replyId : Option ReplyId) :
    lockSet_endpointCall callerTid cnodeRootObjId endpointObjId receiverTid
        none replyId none
      = lockSetExtendOpt
          (lockSetExtendOpt
            (lockSetExtendOpt
              (lockSetOfList
                [(tcbLock callerTid, .write),
                 (cnodeLock cnodeRootObjId, .read),
                 (endpointLock endpointObjId, .write)])
              (receiverTid.map (fun rt => (tcbLock rt, .write))))
            (none : Option (LockId × AccessMode)))
          (replyId.map (fun rid => (replyLock rid, .write))) := rfl

/-- WS-SM SM3.B.3: `lockSet` for `endpointReply` (syscall `.reply`).

Caller TCB (write — clearing blocked state); reply target TCB
(write — transitioning out of `BlockedReply`).

Audit-pass-3 (donation-return extension, audit-pass-4 refinement):
when the replier (=caller) has a `.donated scId originalOwner`
binding, `returnDonatedSchedContext` updates the SC + replier's
TCB + originalOwner's TCB.

In a well-formed kernel state (`ipcInvariantFull`'s
`blockedOnReplyHasTarget` + the donation discipline), the
`originalOwner` field stored in the replier's TCB binding equals
the `replyTargetTid` (the cap's stored target).  However, per
plan §4.1's "union over all paths" requirement and CLAUDE.md's
implement-the-improvement rule, the lockSet declares BOTH
independently — the caller pre-resolves the originalOwner from
the replier's TCB binding and passes it explicitly:

* If `replierTcb.schedContextBinding = .donated scId originalOwner`:
  pass `donatedScId := some scId` AND
  `donatedOriginalOwnerTid := some originalOwner`.
* If `.bound _` or `.unbound`: pass both as `none`.

Under the well-formed invariant where originalOwner ==
replyTargetTid, the `insertOrMerge` lub-merge collapses the
duplicate TCB lock entry (write + write = write).  In a
hypothetical invariant-violation state where they differ, the
lockSet correctly covers both objects. -/
def lockSet_endpointReply (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (replyTargetTid : ThreadId)
    (donatedScId : Option SchedContextId)
    (donatedOriginalOwnerTid : Option ThreadId)
    (replyId : Option ReplyId := none)
    (belowHeadReplyId : Option ReplyId)
    (outerCallerTid : Option ThreadId) : LockSet :=
  let withSc := lockSetExtendOpt
    (lockSetOfList
      [(tcbLock callerTid, .write),
       (cnodeLock cnodeRootObjId, .read),
       (tcbLock replyTargetTid, .write)])
    (donatedScId.map (fun sc => (schedContextLock sc, .write)))
  let withOwner := lockSetExtendOpt withSc
    (donatedOriginalOwnerTid.map (fun ot => (tcbLock ot, .write)))
  -- WS-SM SM6.D: the reply consumes the first-class Reply object
  -- (`consumeReply` writes `reply.caller := none`) under the per-object reply
  -- write-lock (`none` ⇒ definitionally unchanged).
  let withReply := lockSetExtendOpt withOwner
    (replyId.map (fun rid => (replyLock rid, .write)))
  -- **WS-OD OD3.7**: the two objects the pop reads *below* the head, in READ
  -- mode — it inspects them and writes neither.  `replyStackOuterCaller?` reads
  -- the Reply one frame down to find the outer caller, and
  -- `outerCallerAcceptable` reads that caller's TCB to check it is a waiting
  -- donor before the pop binds it.  Both are `none` at every depth this tree
  -- reaches today (`replyStackBelowHeadReads?_of_no_stack`), so this declares
  -- ahead of OD4.4's code rather than widening a live footprint.
  let withBelow := lockSetExtendOpt withReply
    (belowHeadReplyId.map (fun rid => (replyLock rid, AccessMode.read)))
  let withOuter := lockSetExtendOpt withBelow
    (outerCallerTid.map (fun ot => (tcbLock ot, AccessMode.read)))
  -- **WS-OD OD3.5**: and the state-level lock when the reply returns a
  -- donation, because `returnDonatedSchedContext` maintains
  -- `SystemState.scThreadIndex` — an `RHTable` whose insert may rehash, so it
  -- does not decompose by object.  Conditioned on the SchedContext member's own
  -- resolver: no donation, no index write, and the extension is `none` and
  -- reduces definitionally.
  lockSetExtendOpt withOuter
    (if donatedScId.isSome then some (stateLevelLock, AccessMode.write) else none)

/-- WS-SM SM3.B.3: `lockSet` for `replyRecv` (syscall `.replyRecv`).

Combined reply + receive in one transition.  Touches the caller
TCB (write — both reply-clearing and receive-blocking phases), the
endpoint (write — queue mutation in the receive phase), the
prior-call reply target TCB (write — completes the reply), and an
optional new sender TCB (write — if a sender was already
waiting).

Audit-pass-3 (donation-return extension, audit-pass-4 refinement):
the reply phase may return a donated SC from the caller (replier)
to the original owner — same shape as `lockSet_endpointReply`.
The receive phase does NOT initiate donation (donation is
caller-initiated from `endpointCall`, not receiver-initiated).

The caller pre-resolves the donation pair by inspecting the
replier's own TCB binding:

* If `replierTcb.schedContextBinding = .donated scId originalOwner`:
  pass `donatedScId := some scId` AND
  `donatedOriginalOwnerTid := some originalOwner`.
* If `.bound _` or `.unbound`: pass both as `none`.

Under the well-formed invariant where originalOwner ==
replyTargetTid, lub-merge collapses the duplicate TCB lock. -/
def lockSet_replyRecv (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (replyTargetTid : ThreadId)
    (endpointObjId : ObjId) (newSenderTid : Option ThreadId)
    (donatedScId : Option SchedContextId)
    (donatedOriginalOwnerTid : Option ThreadId)
    (replyId : Option ReplyId := none)
    (installsCaps : Bool := false)
    (donationServerTid : Option ThreadId)
    (redonatedScId : Option SchedContextId)
    (belowHeadReplyId : Option ReplyId)
    (outerCallerTid : Option ThreadId) : LockSet :=
  -- PR #873 round 8: `.replyRecv`'s receive leg installs capabilities too (it
  -- runs the same WithCaps transition `.receive` does), so the caller's own
  -- CSpace root takes the same write upgrade, in the same size- and
  -- order-preserving way: a mode on the member, not another optional.
  let withSender := lockSetExtendOpt
    (lockSetOfList
      [(tcbLock callerTid, .write),
       (cnodeLock cnodeRootObjId, if installsCaps then .write else .read),
       (tcbLock replyTargetTid, .write),
       (endpointLock endpointObjId, .write)])
    (newSenderTid.map (fun st => (tcbLock st, .write)))
  let withSc := lockSetExtendOpt withSender
    (donatedScId.map (fun sc => (schedContextLock sc, .write)))
  let withOwner := lockSetExtendOpt withSc
    (donatedOriginalOwnerTid.map (fun ot => (tcbLock ot, .write)))
  -- WS-SM SM6.D: replyRecv consumes the prior Reply object and re-links it to the
  -- next caller (one-object reuse) under the per-object reply write-lock.
  let withReply := lockSetExtendOpt withOwner
    (replyId.map (fun rid => (replyLock rid, .write)))
  -- **WS-OD OD3.5 — the recorded server's own TCB.**  The donation this arm
  -- returns is the *recorded* server's, resolved through `recordedReplyServer?`
  -- (PR #892 review round 6), and `replyRecvReturnDonation` writes that thread's
  -- `schedContextBinding := .unbound`.  On a non-delegated reply the recorded
  -- server *is* `callerTid` and `insertOrMerge`'s key merge collapses the two;
  -- it is a distinct key exactly when the reply capability was delegated, which
  -- is the case this arm previously could not declare at all.
  let withServer := lockSetExtendOpt withReply
    (donationServerTid.map (fun srv => (tcbLock srv, .write)))
  -- **WS-OD OD3.5 — the *second* SchedContext hand-off.**  `replyRecvReturnDonation`
  -- does not stop at the return: when the receive leg dequeues a queued `Call`
  -- it runs `applyCallDonationOnCore nextThread callerTid`, and
  -- `donateSchedContext`'s first store writes the **new** caller's SchedContext
  -- (`boundThread := callerTid`).  That object is provably not `donatedScId` —
  -- two threads cannot be bound to one context — so one `schedContextLock` never
  -- covered both, and this arm wrote a SchedContext under no declared lock while
  -- `.call` declared exactly this member for exactly this write
  -- (`lockSet_endpointCall_donation_extension`).  It is the passive-server
  -- steady state, not an edge case: the receiver is `.unbound` at that point
  -- precisely because the return just made it so.
  let withRedonation := lockSetExtendOpt withServer
    (redonatedScId.map (fun sc => (schedContextLock sc, .write)))
  -- **WS-OD OD3.7 — the two objects the pop reads *below* the head**, in READ
  -- mode.  This is the arm the ceiling was raised for: at call depth ≥ 2 the
  -- return walks one link past the head (`replyStackOuterCaller?`) and then
  -- reads that frame's caller's TCB to validate it (`outerCallerAcceptable`),
  -- and neither object is covered by any member above — the head Reply is
  -- `replyId`, and the outer caller is provably neither of the two threads the
  -- pop rewrites.  The second is a validate-then-commit, so declaring it in
  -- read mode is what closes the time-of-check/time-of-use window on the thread
  -- about to receive a scheduling context.
  let withBelow := lockSetExtendOpt withRedonation
    (belowHeadReplyId.map (fun rid => (replyLock rid, AccessMode.read)))
  let withOuter := lockSetExtendOpt withBelow
    (outerCallerTid.map (fun ot => (tcbLock ot, AccessMode.read)))
  -- **WS-RR RR7.11**: and the CDT maps, for the reason spelled out at
  -- `lockSet_endpointReceive` — this arm's receive leg runs the same WithCaps
  -- receive, so it installs through the same `ipcTransferSingleCap` and writes
  -- the same `SystemState`-level derivation structure.
  -- **WS-OD OD3.5**: the same lock also covers `SystemState.scThreadIndex`,
  -- which *both* hand-offs maintain — an `RHTable` whose insert may rehash, so
  -- it does not decompose by object either.  Hence the disjunction: the write
  -- happens if the receive installs capabilities, or if either donation runs.
  -- All three conditions read the same resolvers the members above do, so the
  -- footprint cannot disagree with itself about what the arm does.
  lockSetExtendOpt withOuter
    (if installsCaps || donatedScId.isSome || redonatedScId.isSome then
       some (stateLevelLock, AccessMode.write) else none)

/-- **WS-RR RR7.11**: a `.replyRecv` whose receive leg installs nothing — and,
since **WS-OD OD3.5**, that also returns no donation, re-donates nothing and
resolves no separate recorded server — is definitionally the pre-RR7.11
footprint.  The three added hypotheses are the three writes OD3.5 declared: drop
any one of them and the state-level member is live, so the equation would be
false rather than merely weaker. -/
@[simp] theorem lockSet_replyRecv_no_caps (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (replyTargetTid : ThreadId)
    (endpointObjId : ObjId) (newSenderTid : Option ThreadId)
    (donatedOriginalOwnerTid : Option ThreadId) (replyId : Option ReplyId) :
    lockSet_replyRecv callerTid cnodeRootObjId replyTargetTid endpointObjId newSenderTid
        none donatedOriginalOwnerTid replyId false none none none none
      = lockSetExtendOpt
          (lockSetExtendOpt
            (lockSetExtendOpt
              (lockSetExtendOpt
                (lockSetOfList
                  [(tcbLock callerTid, .write),
                   (cnodeLock cnodeRootObjId, AccessMode.read),
                   (tcbLock replyTargetTid, .write),
                   (endpointLock endpointObjId, .write)])
                (newSenderTid.map (fun st => (tcbLock st, .write))))
              (none : Option (LockId × AccessMode)))
            (donatedOriginalOwnerTid.map (fun ot => (tcbLock ot, .write))))
          (replyId.map (fun rid => (replyLock rid, .write))) := rfl

/-! ## Notification syscalls (2 transitions) -/

/-- WS-SM SM3.B.3: `lockSet` for `notificationSignal`.

The signaller's TCB does NOT mutate (signal is non-blocking from
caller's perspective) — but we conservatively include it in read
mode since the signal path inspects the caller's identity for
badge attribution.  The notification mutates (waiter dequeue or
badge merge); the optional waiter TCB mutates (wake-up). -/
def lockSet_notificationSignal (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (notificationObjId : ObjId)
    (waiterTid : Option ThreadId)
    (boundEndpoint : Option ObjId := none)
    (boundTcb : Option ThreadId := none)
    -- **WS-OD OD3.10**: the bound TCB's queue neighbours.  The bound delivery
    -- dequeues that TCB with `endpointQueueRemoveDual`, which relinks its
    -- predecessor and its successor -- two TCB *objects* this footprint did not
    -- name, so a `.notificationSignal` on one core and a `.tcbSuspend` of a
    -- queue-mate on another had provably disjoint footprints while both writing
    -- it.  Defaulted, so every non-bound call site is unchanged and reduces
    -- definitionally to the pre-OD3.10 footprint.
    (spliceNeighbors : Option ThreadId × Option ThreadId := (none, none)) : LockSet :=
  -- WS-SM SM6.B/SM6.D (PR #822 Codex review): a notification bound to a TCB
  -- blocked on receive takes the bound-delivery path (`notificationSignalBoundOnCore`):
  -- it dequeues the bound TCB from its endpoint (`endpointQueueRemoveDual` — an
  -- endpoint **write**) and writes the bound TCB (`.ready` + badge — a TCB
  -- **write**).  These two state-dependent writes are folded in as outermost
  -- optionals so the canonical `.notificationSignal` footprint upper-bounds the
  -- bound case.  `none` ⇒ the set is definitionally the non-bound footprint, so
  -- every existing call site is unchanged.  (`permittedKinds .notificationSignal`
  -- already lists `.endpoint`/`.tcb`.)  The state-resolved instance that sets these
  -- optionals from `boundDeliveryTarget?` is `lockSet_notificationSignalOnCore`.
  let withWaiter := lockSetExtendOpt
    (lockSetOfList
      [(tcbLock callerTid, .read),
       (cnodeLock cnodeRootObjId, .read),
       (notificationLock notificationObjId, .write)])
    (waiterTid.map (fun wt => (tcbLock wt, .write)))
  let withEp := lockSetExtendOpt withWaiter
    (boundEndpoint.map (fun ep => (endpointLock ep, .write)))
  let withBound := lockSetExtendOpt withEp
    (boundTcb.map (fun bt => (tcbLock bt, .write)))
  let withPrev := lockSetExtendOpt withBound
    (spliceNeighbors.1.map (fun p => (tcbLock p, AccessMode.write)))
  lockSetExtendOpt withPrev
    (spliceNeighbors.2.map (fun n => (tcbLock n, AccessMode.write)))

/-- **WS-OD OD3.10**: a signal that splices nothing is definitionally the
pre-OD3.10 footprint, so every statement and fixture taken over the
five-argument form survives unchanged. -/
@[simp] theorem lockSet_notificationSignal_no_splice (callerTid : ThreadId)
    (cnodeRootObjId notificationObjId : ObjId) (waiterTid : Option ThreadId)
    (boundEndpoint : Option ObjId) (boundTcb : Option ThreadId) :
    lockSet_notificationSignal callerTid cnodeRootObjId notificationObjId waiterTid
        boundEndpoint boundTcb (none, none)
      = lockSetExtendOpt
          (lockSetExtendOpt
            (lockSetExtendOpt
              (lockSetOfList
                [(tcbLock callerTid, .read),
                 (cnodeLock cnodeRootObjId, .read),
                 (notificationLock notificationObjId, .write)])
              (waiterTid.map (fun wt => (tcbLock wt, .write))))
            (boundEndpoint.map (fun ep => (endpointLock ep, .write))))
          (boundTcb.map (fun bt => (tcbLock bt, .write))) := rfl

/-- WS-SM SM3.B.3: `lockSet` for `notificationWait`.

Caller TCB blocks (write); notification mutates (waiter list
append OR badge consumption); CSpace read. -/
def lockSet_notificationWait (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (notificationObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .write),
     (cnodeLock cnodeRootObjId, .read),
     (notificationLock notificationObjId, .write)]

/-! ## Capability syscalls (4 transitions) -/

/-- WS-SM SM3.B.3: `lockSet` for `cspaceMint`.

Caller TCB (read — non-mutating; cap pointers are derived from
state); source CNode (read — original cap is unchanged); target
CNode (write — minted cap is stored).

**WS-RR RR7.9 — the CDT maps.**  All four capability operations write
`SystemState`-level derivation structure, not only CNode slots: `cspaceMint`,
`cspaceCopy` and `cspaceMove` mint nodes for both endpoints
(`ensureCdtNodeForSlot`, which advances the global `cdtNextNode` counter and
both keyed maps) and add an edge to `cdt`; `cspaceDelete` removes a node.  None
of that decomposes by object, so with per-object members alone two of these on
disjoint CNodes have provably disjoint footprints while allocating from one
counter — the later commit either collides on a node id or loses a slot
mapping.  `stateLevelLock` is the declared subject for `SystemState`-level
auxiliary structures (SM3.A.10), and it is unconditional here because these
operations always write the CDT when they succeed. -/
def lockSet_cspaceMint (callerTid : ThreadId)
    (srcCnodeObjId dstCnodeObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock srcCnodeObjId, .read),
     (cnodeLock dstCnodeObjId, .write),
     (stateLevelLock, .write)]

/-- WS-SM SM3.B.3: `lockSet` for `cspaceCopy`.  Same shape as `mint`,
including WS-RR RR7.9's state-level member — it mints the same two CDT nodes
and adds the same edge. -/
def lockSet_cspaceCopy (callerTid : ThreadId)
    (srcCnodeObjId dstCnodeObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock srcCnodeObjId, .read),
     (cnodeLock dstCnodeObjId, .write),
     (stateLevelLock, .write)]

/-- WS-SM SM6.D / PR #822 Phase H: `lockSet` for `mintReplyCap`.

Derives a `.replyCap` from the `.object`-to-Reply cap at the source slot and installs it
at the destination slot — same CNode footprint as `cspaceCopy` (source CNode read,
destination CNode write, caller TCB read).  It does **not** write the Reply object itself
(only the dst CNode slot), so no `.reply` lock is in the footprint. -/
def lockSet_mintReplyCap (callerTid : ThreadId)
    (srcCnodeObjId dstCnodeObjId : ObjId) : LockSet :=
  lockSet_cspaceCopy callerTid srcCnodeObjId dstCnodeObjId

/-- WS-SM SM3.B.3: `lockSet` for `cspaceMove`.

Both source and destination CNodes are mutated (cap removed from
src, inserted to dst), and — WS-RR RR7.9 — the CDT, exactly as `mint` and
`copy` do. -/
def lockSet_cspaceMove (callerTid : ThreadId)
    (srcCnodeObjId dstCnodeObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock srcCnodeObjId, .write),
     (cnodeLock dstCnodeObjId, .write),
     (stateLevelLock, .write)]

/-- WS-SM SM3.B.3: `lockSet` for `cspaceDelete`.

The target CNode is the object-level mutation; the caller's CSpace root is
read for the cap-lookup path.  WS-RR RR7.9: and the CDT, from the other
direction — a delete **removes** the slot's node (`cdt.removeNode`), which is
the same global structure the three creating operations allocate in. -/
def lockSet_cspaceDelete (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (targetCnodeObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read),
     (cnodeLock targetCnodeObjId, .write),
     (stateLevelLock, .write)]

/-! ## Lifecycle syscalls (1 transition: lifecycleRetype) -/

/-- WS-SM SM3.B.3: `lockSet` for `lifecycleRetype`.

Caller TCB (read), untyped source (write — watermark advance,
child list append), destination CNode (write — caps installed for
the new objects).

**And the re-purposed target's own lock** (PR #873 round 7).  SM9.D.12 made
`.lifecycleRetype` the one arm that *clears* provenance: the plan's `cleared`
list is `[args.targetObj]`, so the commit writes the taint table at that key.
The target is named by the decoded arguments and its type is whatever the state
says — it can be a TCB or a notification concurrently receiving tagged content —
so without this member a retype and a delivery had provably disjoint footprints
while both updating the same taint key, and either the propagation or the clear
could be lost.  A lost clear is the sharper half: the replacement object would
keep a destroyed object's predecessor and a downgrade behind it would report a
chain that ended when the object did.

Supplied by the caller rather than derived here, for the reason
`lockSet_declassify` supplies its target lock: a `LockId` is `⟨kind, objId⟩` and
the kind is a property of the state.  `none` is the unresolved shape and is
definitionally the identity, so every pin taken before this member existed
survives by `rfl`. -/
def lockSet_lifecycleRetype (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (untypedObjId : ObjId)
    (dstCnodeObjId : ObjId) (targetLock : Option LockId := none) : LockSet :=
  lockSetExtendOpt
    (lockSetOfList
      [(tcbLock callerTid, .read),
       (cnodeLock cnodeRootObjId, .read),
       (untypedLock untypedObjId, .write),
       (cnodeLock dstCnodeObjId, .write),
       (stateLevelLock, .write)])
    (targetLock.map (fun l => (l, AccessMode.write)))

/-! ## VSpace syscalls (2 transitions) -/

/-- WS-SM SM3.B.3: `lockSet` for `vspaceMap`. -/
def lockSet_vspaceMap (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (vspaceRootObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read),
     (vspaceRootLock vspaceRootObjId, .write)]

/-- WS-SM SM3.B.3: `lockSet` for `vspaceUnmap`. -/
def lockSet_vspaceUnmap (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (vspaceRootObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read),
     (vspaceRootLock vspaceRootObjId, .write)]

/-- WS-SM SM7.D: `lockSet` for `vspaceUnifyInstruction`.

The VSpaceRoot lock is taken in **read** mode, not write: the unify is a pure
cache operation (`vspaceUnifyInstructionPage_frame` — it modifies no page
table).  It reads the root to resolve the page's physical address, and its only
state effect is on `perCoreICache` and the emission ledger, neither of which is
a per-object lock subject.  This is the one VSpace syscall whose footprint is
read-only on the address space, which is also why it can safely run
concurrently with another subject's unify of a different page. -/
def lockSet_vspaceUnifyInstruction (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (vspaceRootObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read),
     (vspaceRootLock vspaceRootObjId, .read)]

/-! ## Declassification (2 transitions)

`.declassify` is the one syscall whose entire state effect is on a
`SystemState` field rather than on an object: it appends to
`declassificationAuditLog`.  That field is no more a per-object lock subject
than `tlbShootdown` is (SM7.B gave that one its own cross-domain
`TlbShootdownLockId`), so the per-object footprint here covers only the two
universal reads plus the state-level singleton.

WS-SM SM9.C.8's `.declassifySignal` is the *data-carrying* declassification:
it does everything the ordinary `.notificationSignal` does — badge delivery,
waiter wake, the seL4 bound-delivery path — **and** appends one audit entry
per authorized hop.  Its footprint is therefore the union of the two:
`.notificationSignal`'s object-level set, plus the state-level write the
trail append needs.  Stating it as a union rather than as a fresh list is
deliberate: the notification half must never drift from the syscall it wraps
(`lockSet_declassifySignal_extends_notificationSignal` is the tie), and the
state-level half must never be dropped (`lockSet_declassifySignal_stateLevel_write_mem`). -/

/-- WS-SM SM8.C.9: `lockSet` for `declassify`.

**The caller TCB is write mode, and the resolved target carries its own lock.**
An authorized hop appends an audit event, and SM9.D's origination writes that
event's identity into the taint table at two keys — the event's `targetObject`
and the actor's TCB (`taintOriginationKeys`).  Those are taint writes, and the
serialization subject for a taint write is the **key's own object lock**: that is
the whole point of §3d in `TaintPropagation.lean`, which declines to put
`stateLevelLock` on the eight content-moving syscalls because a globally
contended lock on the IPC path is a design regression.

So `stateLevelLock` cannot stand in for those two keys.  It serialises this
transition against other *state-level* writers — another declassification, an
`.auditDrain` — and against nothing else; an ordinary IPC updating the same
object's taint holds only that object's lock and, by that same decision, no
state-level lock at all.  Two such commits would have provably disjoint
footprints while both writing one taint key, and 2PL would admit them
concurrently with one update lost.  Declaring the keys under their own locks is
what makes the two sides meet on the same subject.

The target's lock is supplied by the caller rather than derived here, because a
`LockId` is `⟨kind, objId⟩` and the kind is a property of the *state* — the
declassify capability names `.object targetId` of any kind.  `none` is the
capless/unresolved shape and is definitionally the identity, so every pin taken
before this member existed survives by `rfl`.

Caller CNode stays **read**: capability resolution reads it and nothing keys a
taint write at a CSpace root on this path.  The transition's other write is the
audit-trail append — a `SystemState` field, not an object — and since PR #870
round 7
that write is declared through the **state-level lock** in write mode:
`stateLevelLock` is SM3.A.10's `objStoreLock` singleton, whose acquire
advances `SystemState.objStoreLock` directly, and it is the serialization
subject for the SystemState-level auxiliary structures.  Without it, two
declassifications — or a declassification and an `.auditDrain` — from
different callers had provably disjoint footprints while read-modify-writing
the same trail, so SM3.C.9's fine locks would have admitted a lost append
(the exact failure `declassifyStoreOnCore_never_unaudited` excludes; the
SM5.I kernel-entry lock masks it today).
`auditState_footprints_share_serialization` is the non-disjointness capstone.

The target object is read once, for its kind tag, with no field access — a
read the same state-level member covers.  Either direction of a concurrent
race on it is benign: a target created concurrently makes the check fail and
the syscall return `.objectNotFound`, and a target destroyed concurrently
leaves an audit entry naming an id that no longer resolves — a fidelity
artefact, not an authority one, since the authority came from the
capability. -/
def lockSet_declassify (callerTid : ThreadId) (cnodeRootObjId : ObjId)
    (targetLock : Option LockId := none) : LockSet :=
  lockSetExtendOpt
    (lockSetOfList
      [(tcbLock callerTid, .write),
       (cnodeLock cnodeRootObjId, .read),
       (stateLevelLock, .write)])
    (targetLock.map (fun l => (l, AccessMode.write)))

/-- WS-SM SM9.C.8: `lockSet` for `declassifySignal` — the data-carrying
declassification.

**Defined as** `lockSet_notificationSignal` extended with the state-level
write, rather than as a fresh list.  The transition *is* the ordinary signal
plus an audit append (`declassifiedSignal_ordinary_eq_signal` proves the
unauthorized-hop-free case is literally `notificationSignalOnCore`), so its
object-level footprint must be exactly the signal's: the caller TCB read, the
CSpace root read, the notification write, the woken waiter's TCB write, and —
on the seL4 bound-delivery path — the bound TCB's endpoint write and the bound
TCB's own write.  Writing those out again here would let the two drift the
moment SM6.B's footprint changes; composing them cannot.

The state-level write is the trail append, declared exactly as `.declassify`
declares it (PR #870 round 7): two concurrent declassifying signals, or one
against an `.auditDrain`, read-modify-write the same
`declassificationAuditLog`, and with only per-object members their footprints
are provably disjoint whenever they name different notifications — so a 2PL
consumer would admit a lost append, the failure
`declassifiedSignal_never_unaudited` excludes.  Unlike `.declassify`, this
syscall genuinely writes objects too, so the state-level member is an
*addition* to a non-trivial footprint rather than the whole of it.

The caller TCB stays **read**: the syscall is `.unit`-shaped
(`syscallReturnShape .declassifySignal = .unit`), so unlike the audit pair
there is no `writeReturnFrameToTcb` staging write at the committed dispatch —
the badge this transition moves is delivered to the *receiver*, not returned
to the signaller. -/
def lockSet_declassifySignal (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (notificationObjId : ObjId)
    (waiterTid : Option ThreadId)
    (boundEndpoint : Option ObjId := none)
    (boundTcb : Option ThreadId := none) : LockSet :=
  -- WS-SM SM9.D.17 (audit): the signaller's own TCB is a **write**, and that is
  -- a difference from the plain signal rather than an inherited property.  An
  -- authorized `.declassifySignal` records a hop, and an origination tags the
  -- event's `sourceSubject` — the signaller — so its taint key is written.  The
  -- plain `.notificationSignal` records nothing and correctly holds the caller
  -- read-only, so the upgrade belongs here and not in the footprint it extends.
  --
  -- `stateLevelLock` cannot stand in for it, for the reason §3d of
  -- `TaintPropagation.lean` records: it is deliberately kept off the eight
  -- content-moving syscalls, so an ordinary IPC writing this same TCB's taint
  -- holds only that TCB's lock.  Two such commits would otherwise have provably
  -- disjoint footprints while both writing one taint key.
  --
  -- Merged rather than appended: `insertOrMerge` takes the `AccessMode.lub` of
  -- an existing key, so this upgrades the read the extended footprint already
  -- carries instead of adding a member — the size bound is unchanged.
  lockSetExtendOpt
    (lockSetExtendOpt
      (lockSet_notificationSignal callerTid cnodeRootObjId notificationObjId
        waiterTid boundEndpoint boundTcb)
      (some (stateLevelLock, .write)))
    (some (tcbLock callerTid, AccessMode.write))

/-! ## Audit-trail access (2 transitions)

WS-SM SM9.A.12.  The *transitions'* whole state effect is on `SystemState`
fields — the trail and its epoch — exactly like `.declassify`'s.  But a
declared footprint covers the **committed dispatch**, not the inner transition
alone (PR #870 round 6, the round-4 rule applied to the lock domain): both
audit syscalls are `.word`-shaped, so on success their arms continue into
WS-RA's `writeReturnFrameToTcb`, which **writes the caller's TCB**
(`registerContext` — the staged return frame).  The caller lock is therefore
`.write`; declaring it `.read` would let another TCB writer run concurrently
with the staging write once SM3.C.9 starts consuming these footprints.  The
CNode stays `.read` (capability resolution only).

**And the shared trail itself is a declared subject** (PR #870 round 7): the
reader inspects — and the drain read-modify-writes — the same
`declassificationAuditLog` / `declassificationAuditEpoch` pair that
`.declassify` appends to, so all three footprints carry `stateLevelLock`
(SM3.A.10's SystemState-level singleton): read mode for the reader, write
mode for the drain and the append.  A drain computed from a stale trail
could otherwise discard a concurrently appended record under fine locks —
breaking the exactly-one-record guarantee — with every pairwise footprint
provably disjoint.

The drain additionally requires the `.write` *right* on the audit capability —
a separate gate (`syscallRequiredRight`) and deliberately so: rights bound what
a capability holder may do, lock sets bound what the committed dispatch
touches, and conflating them is how a footprint stops being honest. -/

/-- WS-SM SM9.A.12: `lockSet` for `auditRead`.

Caller TCB **write** (PR #870 round 6): the transition is a pure query over
`declassificationAuditLog`, but the arm stages the returned word into the
caller's TCB via `writeReturnFrameToTcb` — a genuine TCB write the committed
dispatch performs on every success (`lockSet_auditRead_staging_write_mem` ties
it to the footprint by name).  CNode **read** for capability resolution.
State-level lock **read** (PR #870 round 7): the query inspects the shared
trail and epoch — and, since WS-SM SM9.B.10, the refusal ledger, which the
seam read-modify-writes on every recorded refusal — so a concurrent drain's or
refusal's write must exclude against it. -/
def lockSet_auditRead (callerTid : ThreadId) (cnodeRootObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .write),
     (cnodeLock cnodeRootObjId, .read),
     (stateLevelLock, .read)]

/-- WS-SM SM9.A.12: `lockSet` for `auditDrain`.

The reader's caller/CNode pair — the arm stages the returned length into the
caller's TCB (`writeReturnFrameToTcb`), the caller-TCB write the `.write`
mode declares (PR #870 round 6; `lockSet_auditDrain_staging_write_mem`) —
plus the state-level lock in **write** mode (PR #870 round 7): the drain
read-modify-writes `declassificationAuditLog` and
`declassificationAuditEpoch`, and computing the drop from a stale trail while
`.declassify` appends would silently discard the appended record
(`lockSet_auditDrain_stateLevel_write_mem` ties the member to the footprint
by name). -/
def lockSet_auditDrain (callerTid : ThreadId) (cnodeRootObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .write),
     (cnodeLock cnodeRootObjId, .read),
     (stateLevelLock, .write)]

/-- WS-SM SM9.A.12 (PR #870 round 6): the staging write is **in** the declared
footprint — `(tcbLock callerTid, .write)` is a member of the reader's lock set,
by name, so a cut that reverts the caller lock to `.read` stops elaborating
here rather than silently under-declaring the committed dispatch's writes. -/
theorem lockSet_auditRead_staging_write_mem (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) :
    (tcbLock callerTid, AccessMode.write)
      ∈ (lockSet_auditRead callerTid cnodeRootObjId).pairs := by
  unfold lockSet_auditRead lockSetOfList
  simp only [List.foldl]
  exact LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
    (LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
      (by simp [LockSet.insertOrMerge]))

/-- WS-SM SM9.A.12 (PR #870 round 6): the drain's staging write is in its
declared footprint. -/
theorem lockSet_auditDrain_staging_write_mem (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) :
    (tcbLock callerTid, AccessMode.write)
      ∈ (lockSet_auditDrain callerTid cnodeRootObjId).pairs := by
  unfold lockSet_auditDrain lockSetOfList
  simp only [List.foldl]
  exact LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
    (LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
      (by simp [LockSet.insertOrMerge]))

/-- **WS-SM SM9.D: the origination keys ride their own locks, not the trail's.**

An authorized `.declassify` appends an audit event, and the SM9.D origination
writes that event's identity into the taint table at two keys: the event's
`targetObject` and the actor's TCB.  A taint write is serialised by the key's
own object lock — §3d of `TaintPropagation.lean` declines to put
`stateLevelLock` on the content-moving syscalls precisely so the IPC path is not
globally contended — so `stateLevelLock` cannot stand in for either key: it
serialises this transition against other state-level writers and against nothing
else, while an ordinary IPC writing the same key holds only that key's lock.

Both halves are stated separately so the pair cannot silently collapse to one,
and the target half is stated at `some` because that is the shape the resolved
dispatch builds — `none` is the unresolved footprint, which writes no
origination because it names no target. -/
theorem lockSet_declassify_originationKeys_write_mem
    (callerTid : ThreadId) (cnodeRootObjId : ObjId) (targetLock : LockId) :
    (tcbLock callerTid, AccessMode.write)
      ∈ (lockSet_declassify callerTid cnodeRootObjId (some targetLock)).pairs ∧
    (targetLock, AccessMode.write)
      ∈ (lockSet_declassify callerTid cnodeRootObjId (some targetLock)).pairs := by
  constructor
  · unfold lockSet_declassify lockSetExtendOpt lockSetOfList
    simp only [List.foldl, Option.map]
    exact LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
      (LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
        (LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
          (by simp [LockSet.insertOrMerge])))
  · unfold lockSet_declassify lockSetExtendOpt
    simp only [Option.map]
    exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-SM SM9.D (PR #873 round 7): the retype's cleared key rides its own lock
too.**

The sibling of `lockSet_declassify_originationKeys_write_mem`, and the finding it
answers is the same one class over: SM9.D.12 makes `.lifecycleRetype` the arm
that *clears* provenance, and the clear keys on `args.targetObj` — a taint write
like any other, serialised by the key's own object lock.  The declared footprint
named the caller, the caller's root, the untyped source and the destination
CNode, none of which is that key, so a retype and a delivery into the very object
being re-purposed had provably disjoint footprints while updating the same entry.

Stated at `some`, because `none` is the unresolved footprint that names no
target and therefore clears nothing. -/
theorem lockSet_lifecycleRetype_clearedKey_write_mem
    (callerTid : ThreadId) (cnodeRootObjId untypedObjId dstCnodeObjId : ObjId)
    (targetLock : LockId) :
    (targetLock, AccessMode.write)
      ∈ (lockSet_lifecycleRetype callerTid cnodeRootObjId untypedObjId dstCnodeObjId
          (some targetLock)).pairs := by
  unfold lockSet_lifecycleRetype lockSetExtendOpt
  simp only [Option.map]
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- WS-SM SM9.D.17 (audit): the **signalling** declassification writes its
signaller's TCB too.

The sibling of `lockSet_declassify_originationKeys_write_mem`, and it was
missing: `.declassifySignal` extends `lockSet_notificationSignal`, which holds
the caller read-only because a plain signal records no event — but a
declassifying one does, and the origination tags the signaller.  Without this
the declared footprint permitted an ordinary IPC writing the same TCB's taint to
run concurrently, losing one of the two predecessor updates once SM3.C.9 starts
consuming these footprints. -/
theorem lockSet_declassifySignal_originationKeys_write_mem
    (callerTid : ThreadId) (cnodeRootObjId : ObjId) (notificationObjId : ObjId)
    (waiterTid : Option ThreadId) (boundEndpoint : Option ObjId)
    (boundTcb : Option ThreadId) :
    (tcbLock callerTid, AccessMode.write)
      ∈ (lockSet_declassifySignal callerTid cnodeRootObjId notificationObjId
          waiterTid boundEndpoint boundTcb).pairs := by
  unfold lockSet_declassifySignal lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- WS-SM SM9.A.12 (PR #870 round 7): the drain's trail read-modify-write is a
declared **write** on the state-level lock. -/
theorem lockSet_auditDrain_stateLevel_write_mem (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_auditDrain callerTid cnodeRootObjId).pairs := by
  unfold lockSet_auditDrain lockSetOfList
  simp only [List.foldl]
  exact List.mem_cons_self ..

/-- WS-SM SM9.A.12 (PR #870 round 7): the reader's trail inspection is a
declared **read** on the state-level lock, so a concurrent drain's write
excludes against it. -/
theorem lockSet_auditRead_stateLevel_read_mem (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) :
    (stateLevelLock, AccessMode.read)
      ∈ (lockSet_auditRead callerTid cnodeRootObjId).pairs := by
  unfold lockSet_auditRead lockSetOfList
  simp only [List.foldl]
  exact List.mem_cons_self ..

/-- **WS-RR RR7.9**: each of the four capability operations declares the
state-level **write** its CDT mutation needs.

The membership half of the closure.  `cspaceMint`, `cspaceCopy` and
`cspaceMove` mint CDT nodes for both endpoints — advancing the global
`cdtNextNode` counter and both keyed maps — and add an edge; `cspaceDelete`
removes a node.  None of that is keyed by an object, so a footprint of
per-object members alone lets two of these on disjoint CNodes run concurrently
against one counter.

Stated four times rather than once over a shared shape, because the four
footprints are four definitions and a cut that drops the member from any one of
them must stop elaborating here — which is the whole point of pinning a member
rather than trusting a docstring. -/
theorem lockSet_cspaceMint_stateLevel_write_mem (callerTid : ThreadId)
    (srcCnodeObjId dstCnodeObjId : ObjId) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_cspaceMint callerTid srcCnodeObjId dstCnodeObjId).pairs := by
  unfold lockSet_cspaceMint lockSetOfList
  simp only [List.foldl]
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-RR RR7.9**: `cspaceCopy`'s — and so `mintReplyCap`'s, which is defined
as it. -/
theorem lockSet_cspaceCopy_stateLevel_write_mem (callerTid : ThreadId)
    (srcCnodeObjId dstCnodeObjId : ObjId) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_cspaceCopy callerTid srcCnodeObjId dstCnodeObjId).pairs := by
  unfold lockSet_cspaceCopy lockSetOfList
  simp only [List.foldl]
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-RR RR7.9**: `cspaceMove`'s. -/
theorem lockSet_cspaceMove_stateLevel_write_mem (callerTid : ThreadId)
    (srcCnodeObjId dstCnodeObjId : ObjId) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_cspaceMove callerTid srcCnodeObjId dstCnodeObjId).pairs := by
  unfold lockSet_cspaceMove lockSetOfList
  simp only [List.foldl]
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-RR RR7.9**: `cspaceDelete`'s — the removal direction, on the same
global structure the three creating operations allocate in. -/
theorem lockSet_cspaceDelete_stateLevel_write_mem (callerTid : ThreadId)
    (cnodeRootObjId targetCnodeObjId : ObjId) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_cspaceDelete callerTid cnodeRootObjId targetCnodeObjId).pairs := by
  unfold lockSet_cspaceDelete lockSetOfList
  simp only [List.foldl]
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-RR RR7.41**: `cspaceDelete` declares the **target CNode's write lock**.

The member a resolution passing through that CNode must conflict with, and the
half of `cspaceWalk_conflicts_with_delete` that comes from the delete's side.
Stated here, beside the footprint, rather than at the consumer: "what does this
footprint contain" is a question about `lockSet_cspaceDelete`. -/
theorem lockSet_cspaceDelete_target_write_mem (callerTid : ThreadId)
    (cnodeRootObjId targetCnodeObjId : ObjId) :
    (cnodeLock targetCnodeObjId, AccessMode.write)
      ∈ (lockSet_cspaceDelete callerTid cnodeRootObjId targetCnodeObjId).pairs := by
  unfold lockSet_cspaceDelete lockSetOfList
  simp only [List.foldl]
  exact LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
    (LockSet.mem_insertOrMerge_write_self _ _)

/-- **WS-RR RR7.9**: `mintReplyCap` inherits the member, by definition rather
than by repetition. -/
theorem lockSet_mintReplyCap_stateLevel_write_mem (callerTid : ThreadId)
    (srcCnodeObjId dstCnodeObjId : ObjId) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_mintReplyCap callerTid srcCnodeObjId dstCnodeObjId).pairs :=
  lockSet_cspaceCopy_stateLevel_write_mem callerTid srcCnodeObjId dstCnodeObjId

/-- **WS-RR RR7.9**: the four operations' footprints are pairwise
**non-disjoint** — every pair shares the state-level lock, whatever CNodes they
name.

This is the statement `UncoveredLockDomain.cdtNodeAllocation` was registered
for — deleted in the same cut, because a domain entry goes when the domain is
covered — and the reason the member is unconditional.  Two capability operations on
otherwise disjoint CSpaces used to have provably disjoint footprints while both
allocating from `cdtNextNode`; a two-phase-locking consumer is entitled to run
disjoint footprints concurrently, so the later commit would collide on a node
id or lose a slot mapping.  With the member declared, no two of them are ever
disjoint, so no consumer may. -/
theorem capabilityOps_footprints_share_serialization
    (callerA callerB : ThreadId) (srcA dstA srcB dstB : ObjId) :
    ((stateLevelLock, AccessMode.write)
        ∈ (lockSet_cspaceMint callerA srcA dstA).pairs ∧
      (stateLevelLock, AccessMode.write)
        ∈ (lockSet_cspaceCopy callerB srcB dstB).pairs) ∧
    ((stateLevelLock, AccessMode.write)
        ∈ (lockSet_cspaceMove callerA srcA dstA).pairs ∧
      (stateLevelLock, AccessMode.write)
        ∈ (lockSet_cspaceDelete callerB srcB dstB).pairs) :=
  ⟨⟨lockSet_cspaceMint_stateLevel_write_mem callerA srcA dstA,
    lockSet_cspaceCopy_stateLevel_write_mem callerB srcB dstB⟩,
   ⟨lockSet_cspaceMove_stateLevel_write_mem callerA srcA dstA,
    lockSet_cspaceDelete_stateLevel_write_mem callerB srcB dstB⟩⟩

/-! ### WS-RR RR7.11 — the IPC rendezvous write members

The primary write of every IPC arm is the **endpoint or notification queue**,
and the second is the **caller's own TCB** (it blocks, unblocks, or takes a
delivered message).  Neither had a membership theorem on any of the four
endpoint arms: the families that existed covered the *optional* members added by
later cuts — the reply object, the donated SchedContext, the bound-delivery
pair, the capability-transfer destination — because each of those arrived with a
finding attached, while the members present since SM3.B were never stated.

That is the enumeration-versus-derivation shape one level down: a footprint's
declared-write set is only as checked as the members someone thought to pin, and
the unpinned ones are exactly the ones a refactor can silently drop.  These
close it for the arms RR7.11 declares.

All of them are unconditional.  `LockSet.mem_insertOrMerge_write_of_mem_write`
carries a write member through *any* later insertion — a coinciding key merges
under `AccessMode.lub`, whose top is `.write` — so no key-distinctness side
condition is needed, and one that appears in such a statement is a hypothesis
the caller has to discharge for nothing. -/

/-- **WS-RR RR7.11**: the sender's own TCB is a declared write of `.send` — it
blocks when no receiver is waiting and is descheduled from its core. -/
theorem lockSet_endpointSend_caller_tcb_write_mem (callerTid : ThreadId)
    (cnodeRootObjId endpointObjId : ObjId) (receiverTid : Option ThreadId)
    (destCnodeObjId : Option ObjId)
    -- **WS-OD OD3.11**: stated at the queue-structure-neighbour arity.
    (queueNeighbour : Option ThreadId) :
    (tcbLock callerTid, AccessMode.write)
      ∈ (lockSet_endpointSend callerTid cnodeRootObjId endpointObjId receiverTid
          destCnodeObjId queueNeighbour).pairs := by
  unfold lockSet_endpointSend lockSetOfList
  simp only [List.foldl]
  -- The optional extensions are peeled by count rather than by a hand-nested
  -- tower, so a member added to this footprint cannot leave a nesting depth
  -- silently wrong (WS-OD OD3.7).
  repeat apply mem_write_lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
              (LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
                (LockSet.mem_insertOrMerge_write_self _ _))
/-- **WS-RR RR7.11**: and the endpoint itself — the queue mutation that *is* the
rendezvous. -/
theorem lockSet_endpointSend_endpoint_write_mem (callerTid : ThreadId)
    (cnodeRootObjId endpointObjId : ObjId) (receiverTid : Option ThreadId)
    (destCnodeObjId : Option ObjId)
    (queueNeighbour : Option ThreadId) :
    (endpointLock endpointObjId, AccessMode.write)
      ∈ (lockSet_endpointSend callerTid cnodeRootObjId endpointObjId receiverTid
          destCnodeObjId queueNeighbour).pairs := by
  unfold lockSet_endpointSend lockSetOfList
  simp only [List.foldl]
  -- The optional extensions are peeled by count rather than by a hand-nested
  -- tower, so a member added to this footprint cannot leave a nesting depth
  -- silently wrong (WS-OD OD3.7).
  repeat apply mem_write_lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_self _ _
/-- **WS-RR RR7.11**: the caller's TCB is a declared write of `.call`.

The generalisation of `lockSet_endpointCall_caller_tcb_write_mem`, which took a
receiver-distinctness hypothesis it never needed — a receiver that *is* the
caller merges write with write and the member survives, so the hypothesis
excluded a case the conclusion already covers.  That statement is kept, and
proved from this one, because it is cited. -/
theorem lockSet_endpointCall_caller_tcb_write_mem_unconditional (callerTid : ThreadId)
    (cnodeRootObjId endpointObjId : ObjId) (receiverTid : Option ThreadId)
    (donatedScId : Option SchedContextId) (replyId : Option ReplyId)
    (destCnodeObjId : Option ObjId)
    -- **WS-OD OD3.11**: stated at the queue-structure-neighbour arity.
    (queueNeighbour : Option ThreadId) :
    (tcbLock callerTid, AccessMode.write)
      ∈ (lockSet_endpointCall callerTid cnodeRootObjId endpointObjId receiverTid
          donatedScId replyId destCnodeObjId queueNeighbour).pairs := by
  unfold lockSet_endpointCall lockSetOfList
  simp only [List.foldl]
  -- The optional extensions are peeled by count rather than by a hand-nested
  -- tower, so a member added to this footprint cannot leave a nesting depth
  -- silently wrong (WS-OD OD3.7).
  repeat apply mem_write_lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
                  (LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
                    (LockSet.mem_insertOrMerge_write_self _ _))
/-- **WS-RR RR7.11**: and `.call`'s endpoint. -/
theorem lockSet_endpointCall_endpoint_write_mem (callerTid : ThreadId)
    (cnodeRootObjId endpointObjId : ObjId) (receiverTid : Option ThreadId)
    (donatedScId : Option SchedContextId) (replyId : Option ReplyId)
    (destCnodeObjId : Option ObjId)
    (queueNeighbour : Option ThreadId) :
    (endpointLock endpointObjId, AccessMode.write)
      ∈ (lockSet_endpointCall callerTid cnodeRootObjId endpointObjId receiverTid
          donatedScId replyId destCnodeObjId queueNeighbour).pairs := by
  unfold lockSet_endpointCall lockSetOfList
  simp only [List.foldl]
  -- The optional extensions are peeled by count rather than by a hand-nested
  -- tower, so a member added to this footprint cannot leave a nesting depth
  -- silently wrong (WS-OD OD3.7).
  repeat apply mem_write_lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_self _ _
/-- **WS-RR RR7.11**: the receiver's own TCB is a declared write of `.receive` —
it blocks when no sender is waiting, and takes the delivered message when one
is. -/
theorem lockSet_endpointReceive_caller_tcb_write_mem (callerTid : ThreadId)
    (cnodeRootObjId endpointObjId : ObjId) (senderTid : Option ThreadId)
    (replyId : Option ReplyId) (installsCaps : Bool)
    (donatedScId : Option SchedContextId) :
    (tcbLock callerTid, AccessMode.write)
      ∈ (lockSet_endpointReceive callerTid cnodeRootObjId endpointObjId senderTid
          replyId installsCaps donatedScId).pairs := by
  unfold lockSet_endpointReceive lockSetOfList
  simp only [List.foldl]
  -- The optional extensions are peeled by count rather than by a hand-nested
  -- tower, so a member added to this footprint cannot leave a nesting depth
  -- silently wrong (WS-OD OD3.7).
  repeat apply mem_write_lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
                (LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
                  (LockSet.mem_insertOrMerge_write_self _ _))
/-- **WS-RR RR7.11**: and `.receive`'s endpoint. -/
theorem lockSet_endpointReceive_endpoint_write_mem (callerTid : ThreadId)
    (cnodeRootObjId endpointObjId : ObjId) (senderTid : Option ThreadId)
    (replyId : Option ReplyId) (installsCaps : Bool)
    (donatedScId : Option SchedContextId) :
    (endpointLock endpointObjId, AccessMode.write)
      ∈ (lockSet_endpointReceive callerTid cnodeRootObjId endpointObjId senderTid
          replyId installsCaps donatedScId).pairs := by
  unfold lockSet_endpointReceive lockSetOfList
  simp only [List.foldl]
  -- The optional extensions are peeled by count rather than by a hand-nested
  -- tower, so a member added to this footprint cannot leave a nesting depth
  -- silently wrong (WS-OD OD3.7).
  repeat apply mem_write_lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_self _ _
/-- **WS-RR RR7.11**: the replier's own TCB is a declared write of `.reply` — it
is descheduled on its executing core when the answered caller is woken. -/
theorem lockSet_endpointReply_caller_tcb_write_mem (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (replyTargetTid : ThreadId)
    (donatedScId : Option SchedContextId) (donatedOriginalOwnerTid : Option ThreadId)
    (replyId : Option ReplyId)
    (belowHeadReplyId : Option ReplyId) (outerCallerTid : Option ThreadId) :
    (tcbLock callerTid, AccessMode.write)
      ∈ (lockSet_endpointReply callerTid cnodeRootObjId replyTargetTid donatedScId
          donatedOriginalOwnerTid replyId belowHeadReplyId outerCallerTid).pairs := by
  unfold lockSet_endpointReply lockSetOfList
  simp only [List.foldl]
  -- WS-OD OD3.5: a fourth optional extension on the outside — the state-level
  -- lock the donation return's `scThreadIndex` write takes.
  -- The optional extensions are peeled by count rather than by a hand-nested
  -- tower, so a member added to this footprint cannot leave a nesting depth
  -- silently wrong (WS-OD OD3.7).
  repeat apply mem_write_lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
                (LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
                  (LockSet.mem_insertOrMerge_write_self _ _))
/-- **WS-RR RR7.11**: `.replyRecv`'s own TCB — it replies, then receives, and
either blocks or takes the next message. -/
theorem lockSet_replyRecv_caller_tcb_write_mem (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (replyTargetTid : ThreadId) (endpointObjId : ObjId)
    (newSenderTid : Option ThreadId) (donatedScId : Option SchedContextId)
    (donatedOriginalOwnerTid : Option ThreadId) (replyId : Option ReplyId)
    (installsCaps : Bool) (donationServerTid : Option ThreadId)
    (redonatedScId : Option SchedContextId)
    (belowHeadReplyId : Option ReplyId) (outerCallerTid : Option ThreadId) :
    (tcbLock callerTid, AccessMode.write)
      ∈ (lockSet_replyRecv callerTid cnodeRootObjId replyTargetTid endpointObjId
          newSenderTid donatedScId donatedOriginalOwnerTid replyId installsCaps
          donationServerTid redonatedScId belowHeadReplyId outerCallerTid).pairs := by
  unfold lockSet_replyRecv lockSetOfList
  simp only [List.foldl]
  -- WS-OD OD3.5: two further optional extensions on the outside — the recorded
  -- server's TCB and the re-donated SchedContext.
  -- The optional extensions are peeled by count rather than by a hand-nested
  -- tower, so a member added to this footprint cannot leave a nesting depth
  -- silently wrong (WS-OD OD3.7).
  repeat apply mem_write_lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
                      (LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
                        (LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
                          (LockSet.mem_insertOrMerge_write_self _ _)))
/-- **WS-RR RR7.11**: the answered caller's TCB, which the reply leg wakes. -/
theorem lockSet_replyRecv_target_tcb_write_mem (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (replyTargetTid : ThreadId) (endpointObjId : ObjId)
    (newSenderTid : Option ThreadId) (donatedScId : Option SchedContextId)
    (donatedOriginalOwnerTid : Option ThreadId) (replyId : Option ReplyId)
    (installsCaps : Bool) (donationServerTid : Option ThreadId)
    (redonatedScId : Option SchedContextId)
    (belowHeadReplyId : Option ReplyId) (outerCallerTid : Option ThreadId) :
    (tcbLock replyTargetTid, AccessMode.write)
      ∈ (lockSet_replyRecv callerTid cnodeRootObjId replyTargetTid endpointObjId
          newSenderTid donatedScId donatedOriginalOwnerTid replyId installsCaps
          donationServerTid redonatedScId belowHeadReplyId outerCallerTid).pairs := by
  unfold lockSet_replyRecv lockSetOfList
  simp only [List.foldl]
  -- The optional extensions are peeled by count rather than by a hand-nested
  -- tower, so a member added to this footprint cannot leave a nesting depth
  -- silently wrong (WS-OD OD3.7).
  repeat apply mem_write_lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
                      (LockSet.mem_insertOrMerge_write_self _ _)
/-- **WS-RR RR7.11**: and `.replyRecv`'s endpoint, for the receive leg. -/
theorem lockSet_replyRecv_endpoint_write_mem (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (replyTargetTid : ThreadId) (endpointObjId : ObjId)
    (newSenderTid : Option ThreadId) (donatedScId : Option SchedContextId)
    (donatedOriginalOwnerTid : Option ThreadId) (replyId : Option ReplyId)
    (installsCaps : Bool) (donationServerTid : Option ThreadId)
    (redonatedScId : Option SchedContextId)
    (belowHeadReplyId : Option ReplyId) (outerCallerTid : Option ThreadId) :
    (endpointLock endpointObjId, AccessMode.write)
      ∈ (lockSet_replyRecv callerTid cnodeRootObjId replyTargetTid endpointObjId
          newSenderTid donatedScId donatedOriginalOwnerTid replyId installsCaps
          donationServerTid redonatedScId belowHeadReplyId outerCallerTid).pairs := by
  unfold lockSet_replyRecv lockSetOfList
  simp only [List.foldl]
  -- The optional extensions are peeled by count rather than by a hand-nested
  -- tower: `repeat` states "every extension above the base", so a member added
  -- to this footprint does not silently make a nesting depth wrong.
  repeat apply mem_write_lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-RR RR7.11**: `.notificationWait`'s caller TCB — it blocks, or consumes
a pending badge into its own message field. -/
theorem lockSet_notificationWait_caller_tcb_write_mem (callerTid : ThreadId)
    (cnodeRootObjId notificationObjId : ObjId) :
    (tcbLock callerTid, AccessMode.write)
      ∈ (lockSet_notificationWait callerTid cnodeRootObjId notificationObjId).pairs := by
  unfold lockSet_notificationWait lockSetOfList
  simp only [List.foldl]
  exact LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
    (LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
      (LockSet.mem_insertOrMerge_write_self _ _))

/-- **WS-RR RR7.11**: and the notification it waits on, whose waiter list or
badge the wait mutates. -/
theorem lockSet_notificationWait_notification_write_mem (callerTid : ThreadId)
    (cnodeRootObjId notificationObjId : ObjId) :
    (notificationLock notificationObjId, AccessMode.write)
      ∈ (lockSet_notificationWait callerTid cnodeRootObjId notificationObjId).pairs := by
  unfold lockSet_notificationWait lockSetOfList
  simp only [List.foldl]
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-RR RR7.11**: the receive leg's capability install declares the
state-level **write** its CDT mutation needs.

The receive-side half of RR7.7's closure.  `ipcTransferSingleCap` is one
function: whichever arm reaches it, it mints a derivation node for the
destination slot (`ensureCdtNodeForSlot`, advancing the global `cdtNextNode`
counter and both keyed maps) and adds an `.ipcTransfer` edge.  RR7.7 declared
that on `.send` and `.call`; the two receiving arms install through the very
same call and declared it on neither, so a receive dequeuing a caps-bearing
sender was provably disjoint from a concurrent send installing into a different
CSpace while both read-modify-wrote one derivation map.

Conditioned on `installsCaps` because that is the flag the transition itself
branches on (`receiveInstallsCaps`, read from the same pre-state), so the
declared footprint carries the member exactly when the write happens. -/
theorem lockSet_endpointReceive_stateLevel_write_mem (callerTid : ThreadId)
    (cnodeRootObjId endpointObjId : ObjId) (senderTid : Option ThreadId)
    (replyId : Option ReplyId) (donatedScId : Option SchedContextId) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_endpointReceive callerTid cnodeRootObjId endpointObjId senderTid
          replyId true donatedScId).pairs := by
  unfold lockSet_endpointReceive
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-OD OD3.6**: and a receive that donates declares the state-level lock
even when it installs nothing — the passive-server path, where the arm writes
`SystemState.scThreadIndex` and installs no capability at all.  Stated
separately from the caps case because the two are different writes reached by
different conditions; a single statement over `installsCaps = true` would leave
the donating-only arm undeclared, which is the shape this row exists to fix. -/
theorem lockSet_endpointReceive_donation_stateLevel_write_mem (callerTid : ThreadId)
    (cnodeRootObjId endpointObjId : ObjId) (senderTid : Option ThreadId)
    (replyId : Option ReplyId) (installsCaps : Bool) (scId : SchedContextId) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_endpointReceive callerTid cnodeRootObjId endpointObjId senderTid
          replyId installsCaps (some scId)).pairs := by
  unfold lockSet_endpointReceive
  simp only [Option.isSome_some, Bool.or_true, if_true]
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-OD OD3.6**: and the donated SchedContext itself — the object
`donateSchedContext`'s first store writes. -/
theorem lockSet_endpointReceive_donated_sc_write_mem (callerTid : ThreadId)
    (cnodeRootObjId endpointObjId : ObjId) (senderTid : Option ThreadId)
    (replyId : Option ReplyId) (installsCaps : Bool) (scId : SchedContextId) :
    (schedContextLock scId, AccessMode.write)
      ∈ (lockSet_endpointReceive callerTid cnodeRootObjId endpointObjId senderTid
          replyId installsCaps (some scId)).pairs := by
  unfold lockSet_endpointReceive
  exact mem_write_lockSetExtendOpt _ _ _
    (LockSet.mem_insertOrMerge_write_self _ _)

/-- **WS-RR RR7.11**: and `.replyRecv`'s, whose receive leg is the same
WithCaps receive. -/
theorem lockSet_replyRecv_stateLevel_write_mem (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (replyTargetTid : ThreadId) (endpointObjId : ObjId)
    (newSenderTid : Option ThreadId) (donatedScId : Option SchedContextId)
    (donatedOriginalOwnerTid : Option ThreadId) (replyId : Option ReplyId)
    (donationServerTid : Option ThreadId) (redonatedScId : Option SchedContextId) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_replyRecv callerTid cnodeRootObjId replyTargetTid endpointObjId
          newSenderTid donatedScId donatedOriginalOwnerTid replyId true
          donationServerTid redonatedScId belowHeadReplyId outerCallerTid).pairs := by
  unfold lockSet_replyRecv
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-OD OD3.5**: and it is declared for the *donations* too, not only for a
capability install.

`replyRecvReturnDonation` maintains `SystemState.scThreadIndex` on both
hand-offs, and that field is an `RHTable` whose insert may rehash the whole
table.  Stated at `installsCaps = false` precisely so it cannot be read as a
restatement of the theorem above: this is the arm that installs nothing and
still writes state-level structure. -/
theorem lockSet_replyRecv_donation_stateLevel_write_mem (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (replyTargetTid : ThreadId) (endpointObjId : ObjId)
    (newSenderTid : Option ThreadId) (donatedScId : SchedContextId)
    (donatedOriginalOwnerTid : Option ThreadId) (replyId : Option ReplyId)
    (donationServerTid : Option ThreadId) (redonatedScId : Option SchedContextId) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_replyRecv callerTid cnodeRootObjId replyTargetTid endpointObjId
          newSenderTid (some donatedScId) donatedOriginalOwnerTid replyId false
          donationServerTid redonatedScId belowHeadReplyId outerCallerTid).pairs := by
  unfold lockSet_replyRecv
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-OD OD3.5**: the state-level lock is declared for the **second**
hand-off too, not only the return — `applyCallDonation`'s `donateSchedContext`
ends in the same `scThreadIndex` maintenance. -/
theorem lockSet_replyRecv_redonation_stateLevel_write_mem (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (replyTargetTid : ThreadId) (endpointObjId : ObjId)
    (newSenderTid : Option ThreadId) (donatedScId : Option SchedContextId)
    (donatedOriginalOwnerTid : Option ThreadId) (replyId : Option ReplyId)
    (installsCaps : Bool) (donationServerTid : Option ThreadId)
    (redonatedScId : SchedContextId)
    (belowHeadReplyId : Option ReplyId) (outerCallerTid : Option ThreadId) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_replyRecv callerTid cnodeRootObjId replyTargetTid endpointObjId
          newSenderTid donatedScId donatedOriginalOwnerTid replyId installsCaps
          donationServerTid (some redonatedScId) belowHeadReplyId outerCallerTid).pairs := by
  unfold lockSet_replyRecv
  simp only [Option.isSome_some, Bool.or_true, if_true]
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-OD OD3.5**: the **second** SchedContext hand-off's own write lock — the
member whose absence made this footprint false.  `replyRecvReturnDonation`'s
`applyCallDonationOnCore nextThread callerTid` writes the new caller's
SchedContext, which is never the returned one. -/
theorem lockSet_replyRecv_redonated_sc_write_mem (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (replyTargetTid : ThreadId) (endpointObjId : ObjId)
    (newSenderTid : Option ThreadId) (donatedScId : Option SchedContextId)
    (donatedOriginalOwnerTid : Option ThreadId) (replyId : Option ReplyId)
    (installsCaps : Bool) (donationServerTid : Option ThreadId)
    (redonatedScId : SchedContextId)
    (belowHeadReplyId : Option ReplyId) (outerCallerTid : Option ThreadId) :
    (schedContextLock redonatedScId, AccessMode.write)
      ∈ (lockSet_replyRecv callerTid cnodeRootObjId replyTargetTid endpointObjId
          newSenderTid donatedScId donatedOriginalOwnerTid replyId installsCaps
          donationServerTid (some redonatedScId) belowHeadReplyId outerCallerTid).pairs := by
  unfold lockSet_replyRecv
  -- Peeled by an EXACT count, not `repeat`: this member is introduced by an
  -- extension rather than by the base list, so peeling one layer too far would
  -- discard the very lock being proved present.  Three layers sit above it —
  -- the state-level lock and WS-OD OD3.7's two below-head reads.
  iterate 3 apply mem_write_lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-OD OD3.5**: and the **recorded server's** own TCB, which the return
writes `.unbound`.  Distinct from `callerTid` exactly on a delegated reply —
the case this arm previously refused to declare at all. -/
theorem lockSet_replyRecv_donation_server_tcb_write_mem (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (replyTargetTid : ThreadId) (endpointObjId : ObjId)
    (newSenderTid : Option ThreadId) (donatedScId : Option SchedContextId)
    (donatedOriginalOwnerTid : Option ThreadId) (replyId : Option ReplyId)
    (installsCaps : Bool) (donationServerTid : ThreadId)
    (redonatedScId : Option SchedContextId)
    (belowHeadReplyId : Option ReplyId) (outerCallerTid : Option ThreadId) :
    (tcbLock donationServerTid, AccessMode.write)
      ∈ (lockSet_replyRecv callerTid cnodeRootObjId replyTargetTid endpointObjId
          newSenderTid donatedScId donatedOriginalOwnerTid replyId installsCaps
          (some donationServerTid) redonatedScId belowHeadReplyId
          outerCallerTid).pairs := by
  unfold lockSet_replyRecv
  -- An exact count for the same reason as the redonation member above: four
  -- layers sit over the recorded server's own extension — the state-level lock,
  -- WS-OD OD3.7's two below-head reads, and the re-donated SchedContext.
  iterate 4 apply mem_write_lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_self _ _
/-- **WS-RR RR7.11, the capstone: no two capability-installing IPC arms are
ever disjoint.**

`capabilityOps_footprints_share_serialization` one subsystem over, and the
statement the receive side was missing.  The four arms that can reach
`ipcTransferSingleCap` — a send, a call, a receive and a `replyRecv` — all
declare the same state-level write, so a 2PL consumer can never hold two of
their footprints at once.  Before this the sending pair did and the receiving
pair did not, which is worse than neither: the two halves of one rendezvous
disagreed about whether the derivation map they both write is shared state. -/
theorem capsCarryingIpcArms_footprints_share_serialization
    (sender receiver : ThreadId) (cnRootA cnRootB epA epB destRoot : ObjId)
    (receiverTid : Option ThreadId) (senderTid : Option ThreadId)
    (replyIdA replyIdB : Option ReplyId) :
    ((stateLevelLock, AccessMode.write)
        ∈ (lockSet_endpointSend sender cnRootA epA receiverTid (some destRoot)).pairs ∧
      (stateLevelLock, AccessMode.write)
        ∈ (lockSet_endpointReceive receiver cnRootB epB senderTid replyIdA true none).pairs) ∧
    ((stateLevelLock, AccessMode.write)
        ∈ (lockSet_endpointCall sender cnRootA epA receiverTid none replyIdB
             (some destRoot)).pairs ∧
      (stateLevelLock, AccessMode.write)
        ∈ (lockSet_replyRecv receiver cnRootB receiver epB senderTid none none
             replyIdA true none none none none).pairs) :=
  ⟨⟨by unfold lockSet_endpointSend
       exact LockSet.mem_insertOrMerge_write_self _ _,
    lockSet_endpointReceive_stateLevel_write_mem receiver cnRootB epB senderTid replyIdA none⟩,
   ⟨by unfold lockSet_endpointCall
       exact LockSet.mem_insertOrMerge_write_self _ _,
    lockSet_replyRecv_stateLevel_write_mem receiver cnRootB receiver epB senderTid
      none none replyIdA none none⟩⟩

/-- WS-SM SM8.C.9 (PR #870 round 7): the declassification's trail append is a
declared **write** on the state-level lock. -/
theorem lockSet_declassify_stateLevel_write_mem (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_declassify callerTid cnodeRootObjId).pairs := by
  unfold lockSet_declassify lockSetOfList
  simp only [List.foldl]
  exact List.mem_cons_self ..

/-- WS-SM SM9.C.8: the declassifying signal's trail append is a declared
**write** on the state-level lock.

The half of `lockSet_declassifySignal` that `lockSet_notificationSignal` does
not supply.  A cut that drops the extension — reverting the footprint to the
plain signal's — stops elaborating here rather than silently letting two
concurrent declassifying signals race on the trail. -/
theorem lockSet_declassifySignal_stateLevel_write_mem (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (notificationObjId : ObjId)
    (waiterTid : Option ThreadId) (boundEndpoint : Option ObjId)
    (boundTcb : Option ThreadId) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_declassifySignal callerTid cnodeRootObjId notificationObjId
          waiterTid boundEndpoint boundTcb).pairs := by
  unfold lockSet_declassifySignal lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
    (LockSet.mem_insertOrMerge_write_self _ _)

/-- WS-SM SM9.C.8: the declassifying signal's footprint **contains** the
ordinary signal's — every write mode member of the wrapped syscall's set is a
member here.

The other half of the composition, and the one that keeps the two from
drifting: the transition really does perform the ordinary signal's writes
(`declassifiedSignal_ordinary_eq_signal` proves the no-downgrade case is
literally `notificationSignalOnCore`), so under-declaring them would let a
concurrent IPC writer run against a badge delivery.  Stated over write-mode
members because those are the ones exclusion is about; the read members ride
`mem_insertOrMerge_of_mem_of_ne` on the same argument (`stateLevelLock` is
distinct from every per-object key). -/
theorem lockSet_declassifySignal_extends_notificationSignal
    (callerTid : ThreadId) (cnodeRootObjId : ObjId) (notificationObjId : ObjId)
    (waiterTid : Option ThreadId) (boundEndpoint : Option ObjId)
    (boundTcb : Option ThreadId) (l : LockId)
    (hMem : (l, AccessMode.write)
      ∈ (lockSet_notificationSignal callerTid cnodeRootObjId notificationObjId
          waiterTid boundEndpoint boundTcb).pairs) :
    (l, AccessMode.write)
      ∈ (lockSet_declassifySignal callerTid cnodeRootObjId notificationObjId
          waiterTid boundEndpoint boundTcb).pairs := by
  unfold lockSet_declassifySignal lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
    (LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _ hMem)

/-- WS-SM SM9.A.12 (PR #870 round 7, **the non-disjointness capstone**;
extended by SM9.C.8): every footprint that touches the audit trail shares the
state-level lock — write mode at all three writers, read mode at the reader —
for **every** combination of caller TCBs, CSpace roots and notification ids.

This is the fact the round-7 finding said was missing: with only per-object
members, `.declassify` from one caller and `.auditDrain` from another had
provably disjoint footprints while read-modify-writing the same trail, so a
2PL consumer of the declared sets would have admitted a lost append.  With
the shared member, any pair among {append, signal-append, drain} × {append,
signal-append, drain, read} on distinct callers has a write-mode intersection
on `stateLevelLock`, which is exactly what two-phase locking serializes.

`.declassifySignal` is the fourth conjunct and the one whose omission would be
easiest to miss: its footprint is *dominated* by object-level members (a
notification write, a waiter TCB write, possibly an endpoint and a bound TCB),
so unlike the other three it looks like an ordinary IPC syscall — and two
declassifying signals on *different* notifications would then have disjoint
sets while appending to the same trail. -/
theorem auditState_footprints_share_serialization :
    ∀ (callerA : ThreadId) (rootA : ObjId) (callerB : ThreadId) (rootB : ObjId)
      (callerC : ThreadId) (rootC : ObjId)
      (callerD : ThreadId) (rootD : ObjId) (ntfnD : ObjId)
      (waiterD : Option ThreadId) (epD : Option ObjId) (boundD : Option ThreadId),
      (stateLevelLock, AccessMode.write) ∈ (lockSet_declassify callerA rootA).pairs ∧
      (stateLevelLock, AccessMode.write) ∈ (lockSet_auditDrain callerB rootB).pairs ∧
      (stateLevelLock, AccessMode.read) ∈ (lockSet_auditRead callerC rootC).pairs ∧
      (stateLevelLock, AccessMode.write)
        ∈ (lockSet_declassifySignal callerD rootD ntfnD waiterD epD boundD).pairs :=
  fun callerA rootA callerB rootB callerC rootC callerD rootD ntfnD waiterD epD boundD =>
    ⟨lockSet_declassify_stateLevel_write_mem callerA rootA,
     lockSet_auditDrain_stateLevel_write_mem callerB rootB,
     lockSet_auditRead_stateLevel_read_mem callerC rootC,
     lockSet_declassifySignal_stateLevel_write_mem callerD rootD ntfnD waiterD epD boundD⟩

/-- WS-SM SM9.B.9 (**the refusal ledger's serialization subject**): the syscall
whose refusals the seam records declares the state-level lock in **write** mode.

The ledger is a `SystemState` field, like the audit trail, and it is written on
the *error* path of the very syscall whose footprint this is — so under
SM3.C.9's fine locks two concurrent refused declassifications would otherwise
hold provably disjoint sets while read-modify-writing the same ring, losing a
record.  `lockSet_declassify` already carries `(stateLevelLock, .write)` for its
trail append, and the same member covers the ledger.

The first conjunct is what makes this a *gate* rather than a coincidence: it
enumerates **every** syscall the seam records, so a new recording syscall — one
the total `refusalSeamClass` forces its author to classify — breaks this
theorem and has to declare its own state-level write here before it can be
added.  It did exactly that at SM9.C.8: `.declassifySignal` joined the recorded
class, this conjunct stopped being a singleton, and the second and third
conjuncts are the two footprints that now carry the member.

**Which bracket this assumes, stated rather than left implicit.**  The refusal
write happens at the FFI boundary, *after* `syscallEntryChecked` returns its
error — so this member covers it only if SM3.C.9 installs `withLockSet` around
the **committed dispatch** (the `@[export]` body) rather than around the inner
transition alone.  That is already the rule PR #870 rounds 4 and 6 established
for the audit pair — a declared footprint covers what the dispatch commits, not
what the transition writes — and it is the constraint this footprint places on
SM3.C.9's installation point. -/
theorem lockSet_refusalSeam_writer_declares_stateLevel_write
    (callerTid : ThreadId) (cnodeRootObjId : ObjId) (notificationObjId : ObjId)
    (waiterTid : Option ThreadId) (boundEndpoint : Option ObjId)
    (boundTcb : Option ThreadId) :
    (∀ sid : SeLe4n.Model.SyscallId,
      SeLe4n.Kernel.refusalSeamClass sid = .records →
        sid = .declassify ∨ sid = .declassifySignal) ∧
    (stateLevelLock, AccessMode.write) ∈ (lockSet_declassify callerTid cnodeRootObjId).pairs ∧
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_declassifySignal callerTid cnodeRootObjId notificationObjId
          waiterTid boundEndpoint boundTcb).pairs :=
  ⟨fun sid h => (SeLe4n.Kernel.refusalSeamClass_records_iff sid).mp h,
   lockSet_declassify_stateLevel_write_mem callerTid cnodeRootObjId,
   lockSet_declassifySignal_stateLevel_write_mem callerTid cnodeRootObjId
     notificationObjId waiterTid boundEndpoint boundTcb⟩

/-! ## Service syscalls (3 transitions)

Services are tracked at the SystemState level (not as per-object
RHTable entries).  At SM3.B per-object level, the caller TCB and the
relevant CNode are the universal locks; `serviceRegister` additionally
takes a read lock on the endpoint capability target (audit-pass-6
closure).

**Closed at `v0.34.74` (WS-RR RR7.23)**: this header used to claim the registry
reads/writes were covered by the table-level `objStoreLock` "implicitly" — a
convention, not a declared footprint member, so under SM3.C.9's fine locks
nothing would have acquired it and two concurrent `serviceRegister`s had
provably disjoint sets while writing the same `serviceRegistry` map.  The same
defect class the round-7 finding closed for the audit trail, and closed the same
way: all four registry writers now carry `stateLevelLock` by name — the trio in
write / write / **read** mode (the query folds over the whole map, so it is the
reader, exactly as `lockSet_auditRead` is for the trail) and the **retype**,
whose `cleanupEndpointServiceRegistrations` sweep is the writer the prose kept
listing and no footprint declared.  `serviceRegistry_footprints_share_serialization`
is the pin, and a new registry writer must extend it before it can claim a
footprint.  Under the SM5.I kernel-entry lock there was no live race, which is
why the register graded it a medium rather than a blocker. -/

/-- WS-SM SM3.B.3: `lockSet` for `serviceRegister`.

Audit-pass-6 (P2 closure for chatgpt-codex-connector review on PR #793):
`Kernel.Service.Registry.registerService` reads
`st.objects[epId]?` to verify the target object is a `.endpoint`
variant (R4-C.2 / L-09) and the endpoint capability has Write right
(R4-C.1 / M-14).  Without locking the endpoint, this transition
could race with concurrent endpoint writers (e.g., IPC queue
mutations from `endpointSend` / `endpointReceive`) and observe a
mid-transition `KernelObject` variant.  A read lock is sufficient
since `registerService` only writes the `serviceRegistry` map (not
the endpoint object itself). -/
def lockSet_serviceRegister (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (endpointObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read),
     (endpointLock endpointObjId, .read),
     (stateLevelLock, .write)]

/-- WS-SM SM3.B.3: `lockSet` for `serviceRevoke`.

`revokeService sid` only touches `serviceRegistry` (erase) and
`removeDependenciesOf` (in-place state mutation).  Neither reads
nor writes a kernel object, so the per-object lock footprint is
just caller TCB + CNode. -/
def lockSet_serviceRevoke (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read),
     (stateLevelLock, .write)]

/-- WS-SM SM3.B.3: `lockSet` for `serviceQuery`.

`lookupServiceByCap epId` folds over `serviceRegistry`; it does NOT
read `st.objects[epId]?` (the lookup is by cap-target ObjId match
within the registry, not by object dereference).

Caller TCB **write** (PR #870 round 6): `.serviceQuery` is `.word`-shaped, so
on success its arm stages the resolved `ServiceId` into the caller's TCB via
WS-RA's `writeReturnFrameToTcb` — the same committed-dispatch caller write the
audit pair declares, present since the WS-RA staging landed (v0.33.37) and
fixed with them (`lockSet_serviceQuery_staging_write_mem`).  CNode **read**
for capability resolution. -/
def lockSet_serviceQuery (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .write),
     (cnodeLock cnodeRootObjId, .read),
     (stateLevelLock, .read)]

/-- WS-SM SM3.B.3 (PR #870 round 6): `.serviceQuery`'s staging write is in its
declared footprint — the sibling of `lockSet_auditRead_staging_write_mem`. -/
theorem lockSet_serviceQuery_staging_write_mem (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) :
    (tcbLock callerTid, AccessMode.write)
      ∈ (lockSet_serviceQuery callerTid cnodeRootObjId).pairs := by
  unfold lockSet_serviceQuery lockSetOfList
  simp only [List.foldl]
  exact LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
    (LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
      (by simp [LockSet.insertOrMerge]))

/-- **WS-RR RR7.23 (register finding 5): every writer of the service registry
declares the state-level lock.**

`SystemState.serviceRegistry` is a state-level map, exactly like the audit
trail, and no per-object lock kind can name it.  Until this cut the three
service footprints and the retype's carried a *convention* — the header above
this file's service section said the registry was covered by the table-level
object-store lock "implicitly" — which under SM3.C.9's fine locks is nothing at
all: two concurrent `serviceRegister`s had provably disjoint sets while
read-modify-writing the same map, and so did a `serviceRevoke` racing a retype
that swept the registry through `cleanupEndpointServiceRegistrations`.

Four writers, and the fourth is the one prose kept forgetting: the **retype**
sweeps the registry when the object it re-purposes is an endpoint, and detaches
the CDT slot mapping when it is a CNode.  Both are state-level maps; neither is
reachable from a per-object footprint.

The query is the reader — `lookupServiceByCap` folds over the whole map — so it
takes the member in **read** mode, exactly as `lockSet_auditRead` does for the
trail.  Read/read does not conflict, so two queries still run concurrently;
what the member buys is that a query cannot observe a half-applied register or
revoke.

A new registry writer must extend this theorem before it can claim a
footprint. -/
theorem serviceRegistry_footprints_share_serialization :
    ∀ (callerA : ThreadId) (rootA epA : ObjId)
      (callerB : ThreadId) (rootB : ObjId)
      (callerC : ThreadId) (rootC : ObjId)
      (callerD : ThreadId) (rootD untypedD dstD : ObjId) (targetD : Option LockId),
      (stateLevelLock, AccessMode.write)
        ∈ (lockSet_serviceRegister callerA rootA epA).pairs ∧
      (stateLevelLock, AccessMode.write)
        ∈ (lockSet_serviceRevoke callerB rootB).pairs ∧
      (stateLevelLock, AccessMode.read)
        ∈ (lockSet_serviceQuery callerC rootC).pairs ∧
      (stateLevelLock, AccessMode.write)
        ∈ (lockSet_lifecycleRetype callerD rootD untypedD dstD targetD).pairs := by
  intro callerA rootA epA callerB rootB callerC rootC callerD rootD untypedD dstD targetD
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold lockSet_serviceRegister lockSetOfList; simp only [List.foldl]
    exact LockSet.mem_insertOrMerge_write_self _ _
  · unfold lockSet_serviceRevoke lockSetOfList; simp only [List.foldl]
    exact LockSet.mem_insertOrMerge_write_self _ _
  · unfold lockSet_serviceQuery lockSetOfList; simp only [List.foldl]
    exact List.mem_cons_self ..
  · refine mem_write_lockSetExtendOpt _ _ _ ?_
    show (stateLevelLock, AccessMode.write) ∈ (lockSetOfList _).pairs
    unfold lockSetOfList
    simp only [List.foldl]
    exact LockSet.mem_insertOrMerge_write_self _ _

/-! ## SchedContext syscalls (3 transitions) -/

/-- WS-SM SM3.B.3: `lockSet` for `schedContextConfigure`.

The SchedContext mutates (budget/period/priority/deadline fields);
its bound TCB (if any) may need its `domain` field rewritten to
match the new SC domain (per the R5.G domain-propagation block). -/
def lockSet_schedContextConfigure (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (scid : SchedContextId)
    (boundTcbTid : Option ThreadId)
    (queueOwner : Option QueueOwner) : LockSet :=
  lockSetExtendOpt
    (lockSetExtendOpt
      (lockSetOfList
        [(tcbLock callerTid, .read),
         (cnodeLock cnodeRootObjId, .read),
         (schedContextLock scid, .write)])
      (boundTcbTid.map (fun bt => (tcbLock bt, .write))))
    (queueOwnerMember queueOwner)

/-- WS-SM SM3.B.3: `lockSet` for `schedContextBind`. -/
def lockSet_schedContextBind (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (scid : SchedContextId)
    (targetTcbTid : ThreadId)
    (queueOwner : Option QueueOwner) : LockSet :=
  -- **WS-OD OD3.5**: `stateLevelLock`, unconditionally — a successful bind ends
  -- in `scThreadIndexAdd`, and `SystemState.scThreadIndex` is an `RHTable`
  -- whose insert may rehash and back-shift the whole table.  Unconditional
  -- because the index write is not optional on the success path, which is the
  -- same shape `lockSet_cspaceMint` uses for the CDT.
  lockSetExtendOpt
    (lockSetOfList
      [(tcbLock callerTid, .read),
       (cnodeLock cnodeRootObjId, .read),
       (schedContextLock scid, .write),
       (tcbLock targetTcbTid, .write),
       (stateLevelLock, .write)])
    (queueOwnerMember queueOwner)

/-- WS-SM SM3.B.3: `lockSet` for `schedContextUnbind`.

**WS-OD OD3.5**: with `stateLevelLock`, for the reason given at
`lockSet_schedContextBind` — the unbind's `scThreadIndexRemove` writes the same
`RHTable`. -/
def lockSet_schedContextUnbind (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (scid : SchedContextId)
    (targetTcbTid : ThreadId)
    (queueOwner : Option QueueOwner) : LockSet :=
  lockSetExtendOpt
    (lockSetOfList
      [(tcbLock callerTid, .read),
       (cnodeLock cnodeRootObjId, .read),
       (schedContextLock scid, .write),
       (tcbLock targetTcbTid, .write),
       (stateLevelLock, .write)])
    (queueOwnerMember queueOwner)

/-- WS-SM SM6.B: `lockSet` for `tcbBindNotification`.  The bound TCB (write —
`boundNotification`) and the notification (write — `boundTCB`) both mutate; the
caller TCB is read (identity) and the CSpace root read (cap resolution). -/
def lockSet_tcbBindNotification (callerTid : ThreadId) (cnodeRootObjId : ObjId)
    (notificationObjId : ObjId) (targetTcbTid : ThreadId)
    (queueOwner : Option QueueOwner) : LockSet :=
  lockSetExtendOpt
    (lockSetOfList
      [(tcbLock callerTid, .read),
       (cnodeLock cnodeRootObjId, .read),
       (notificationLock notificationObjId, .write),
       (tcbLock targetTcbTid, .write)])
    (queueOwnerMember queueOwner)

/-- WS-SM SM6.B: `lockSet` for `tcbUnbindNotification` — same footprint as bind
(both ends of the binding cleared under write locks). -/
def lockSet_tcbUnbindNotification (callerTid : ThreadId) (cnodeRootObjId : ObjId)
    (notificationObjId : ObjId) (targetTcbTid : ThreadId)
    (queueOwner : Option QueueOwner) : LockSet :=
  lockSetExtendOpt
    (lockSetOfList
      [(tcbLock callerTid, .read),
       (cnodeLock cnodeRootObjId, .read),
       (notificationLock notificationObjId, .write),
       (tcbLock targetTcbTid, .write)])
    (queueOwnerMember queueOwner)

/-! ## TCB lifecycle and config syscalls (5 transitions) -/

/-- WS-SM SM3.B.3: `lockSet` for `tcbSuspend`.

Target TCB (write — state transition to `.Inactive`); optional
endpoint/notification if the target is blocked on one (write —
queue removal).

Audit-pass-3 (donation-cancel extension): `cancelDonation`
dispatches on the suspended TCB's `schedContextBinding`:

* `.unbound`: no extra locks.
* `.bound scId`: writes the SC (clears `boundThread`,
  `isActive`).  Caller passes `bindingScId := some scId`.
* `.donated scId originalOwner`: writes the SC + the original
  owner's TCB (re-binds SC to original owner).  Caller passes
  both `bindingScId := some scId` AND
  `donatedOriginalOwnerTid := some originalOwner`.

The caller pre-resolves these by inspecting the suspended TCB's
`schedContextBinding` field before computing the lockSet.

WS-SM SM6.E (reply-link teardown extension): a target that is
`.blockedOnReply` with a live `replyObject` forward link has that
link consumed during suspension (`cancelIpcBlocking` →
`consumeReplyLink` clears `reply.caller`), so the footprint carries
an optional **reply write lock**.  The caller pre-resolves
`consumedReplyId` from the target TCB (`.blockedOnReply` ∧
`replyObject = some rid` → `some rid`); the parameter defaults to
`none` so pre-SM6.E call sites (no reply-blocked target) are
unchanged.

**Size (PR #864 review round 5, restated at WS-OD OD3.5).**  Three base
members plus six optional ones is 9 at full resolution, against a
`maxLockSetSize` of 11.  When this paragraph was written the two numbers
were both 8 and the set sat at the cap, so "this set cannot grow" was an
arithmetic fact; OD3.5 raised the ceiling to declare the members
`.replyRecv` was missing, and the sixth optional here — the state-level
lock the donation cancellation's `scThreadIndex` write takes — is the one
member this set has grown since.  Two slots of headroom is not an
invitation: the constant is the WCRT headline
(`maxLockSetSize · (numCores − 1) · tCs`, and `admissibleCriticalSection`
reads 30 µs off it for the 1 ms tick), so a member added here still costs
every syscall that acquires this footprint.

The question comes up because suspending a victim that sits *inside* an
endpoint queue splices it out and patches its **neighbours'** queue links,
and this set carries no `tcbLock` for either neighbour — whereas the
sub-operation footprint `lockSet_cancelIpcBlockingOnCore` names both
(via `cancelArmSpliceNeighbors?`, which since OD3.5 resolves them on the
splicing arm alone).  The two are reconciled by the queue-owning-object
discipline, not by a missing member: an endpoint owns its queue, so its
**write** lock — which this set does declare whenever the victim is
endpoint-blocked — authorizes the link writes of every TCB in that queue,
and WS-RR RR7.38 made that authorization an *exclusion* by requiring the
same lock of every footprint that can write a queued TCB.  The
sub-operation form names the neighbours because it is the finer-grained
authority the runtime bracket acquires; this one sits under the coarser
umbrella.  Both are sound at their own granularity, and the two members
would now fit — see `suspendFootprint_splice_neighbors_under_endpoint_lock`
for why fitting is not the reason to add them.

That is a checked fact rather than a convention:
`suspendFootprint_splice_neighbors_under_endpoint_lock` (SM8.D) proves it
over the *resolved* footprint and names the neighbours through the same
`queueSpliceNeighbors?`, extending the `lockSet_tcbSuspend_*_write_mem`
family past the six members that stopped exactly where the umbrella
began.  See `IPC/CrossCore/Cancellation.lean` §"Neighbour-lock convention
bridge". -/
def lockSet_tcbSuspend (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (targetTcbTid : ThreadId)
    (blockedEndpointObjId : Option ObjId)
    (blockedNotificationObjId : Option ObjId)
    (bindingScId : Option SchedContextId)
    (donatedOriginalOwnerTid : Option ThreadId)
    (consumedReplyId : Option ReplyId := none) : LockSet :=
  let base := lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read),
     (tcbLock targetTcbTid, .write)]
  let withEp := lockSetExtendOpt base
    (blockedEndpointObjId.map (fun ep => (endpointLock ep, .write)))
  let withN := lockSetExtendOpt withEp
    (blockedNotificationObjId.map (fun n => (notificationLock n, .write)))
  let withSc := lockSetExtendOpt withN
    (bindingScId.map (fun sc => (schedContextLock sc, .write)))
  let withOwner := lockSetExtendOpt withSc
    (donatedOriginalOwnerTid.map (fun ot => (tcbLock ot, .write)))
  let withReply := lockSetExtendOpt withOwner
    (consumedReplyId.map (fun r => (replyLock r, .write)))
  -- **WS-OD OD3.5**: a suspend that cancels a donation runs `cancelDonation`
  -- (or, on a `.blockedOnReply` victim, `returnDonationToCancelledCaller`), and
  -- both maintain `SystemState.scThreadIndex` — an `RHTable` whose insert may
  -- rehash the whole table, so it does not decompose by object.  Conditioned on
  -- the SchedContext member's own resolver, so the two answer one question.
  lockSetExtendOpt withReply
    (if bindingScId.isSome then some (stateLevelLock, AccessMode.write) else none)

/-- WS-SM SM3.B.3: `lockSet` for `tcbResume`.

Target TCB (write — state transition to `.Ready`).  The scheduler
state (run queue) mutates implicitly through the TCB's `objects`
write at SM3.B; SM4 will lift the scheduler to per-core state. -/
def lockSet_tcbResume (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (targetTcbTid : ThreadId)
    (queueOwner : Option QueueOwner) : LockSet :=
  lockSetExtendOpt
    (lockSetOfList
      [(tcbLock callerTid, .read),
       (cnodeLock cnodeRootObjId, .read),
       (tcbLock targetTcbTid, .write)])
    (queueOwnerMember queueOwner)

/-- WS-SM SM3.B.3: `lockSet` for `tcbSetPriority`.

Audit-pass-6 (P1 closure for chatgpt-codex-connector review on PR #793):
`SchedContext.PriorityManagement.setPriorityOp` calls
`updatePrioritySource st tid targetTcb newPriority` which dispatches
on `targetTcb.schedContextBinding`:

* `.unbound`: writes the TARGET TCB's `priority` field (already
  covered by `tcbLock targetTcbTid .write` in the base).
* `.bound scId` / `.donated scId _`: writes the bound SchedContext's
  `priority` field via `st.objects.insert scId.toObjId (.schedContext sc')`.
  Without locking that SC, this transition could race with concurrent
  SchedContext operations on the same object.

The caller pre-resolves `targetTcb.schedContextBinding` to determine
whether the bound SC needs locking:

```
let scId := s.getTcb? targetTcbTid >>= fun t =>
  match t.schedContextBinding with
  | .unbound => none
  | .bound id | .donated id _ => some id
```
-/
def lockSet_tcbSetPriority (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (targetTcbTid : ThreadId)
    (boundSchedContextId : Option SchedContextId)
    (queueOwner : Option QueueOwner) : LockSet :=
  lockSetExtendOpt
    (lockSetExtendOpt
      (lockSetOfList
        [(tcbLock callerTid, .read),
         (cnodeLock cnodeRootObjId, .read),
         (tcbLock targetTcbTid, .write)])
      (boundSchedContextId.map (fun sc => (schedContextLock sc, .write))))
    (queueOwnerMember queueOwner)

/-- WS-SM SM3.B.3: `lockSet` for `tcbSetMCPriority`.

Audit-pass-6 (P1 closure for chatgpt-codex-connector review on PR #793):
`SchedContext.PriorityManagement.setMCPriorityOp` always writes the
target TCB's `maxControlledPriority` field (covered by
`tcbLock targetTcbTid .write` in the base).  In the priority-capping
branch (when the target's current effective priority exceeds
`newMCP`), it then calls `updatePrioritySource` with the capped
priority — which writes the bound SchedContext if the binding is
`.bound`/`.donated` (same shape as `setPriorityOp`).

The caller pre-resolves `targetTcb.schedContextBinding` identically
to `lockSet_tcbSetPriority`. -/
def lockSet_tcbSetMCPriority (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (targetTcbTid : ThreadId)
    (boundSchedContextId : Option SchedContextId)
    (queueOwner : Option QueueOwner) : LockSet :=
  lockSetExtendOpt
    (lockSetExtendOpt
      (lockSetOfList
        [(tcbLock callerTid, .read),
         (cnodeLock cnodeRootObjId, .read),
         (tcbLock targetTcbTid, .write)])
      (boundSchedContextId.map (fun sc => (schedContextLock sc, .write))))
    (queueOwnerMember queueOwner)

/-- WS-SM SM3.B.3: `lockSet` for `tcbSetIPCBuffer`.

Audit-pass-6 (P1 closure for chatgpt-codex-connector review on PR #793):
`Architecture.IpcBufferValidation.setIPCBufferOp` calls
`validateIpcBufferAddress` which reads:

1. `st.getVSpaceRoot? targetTcb.vspaceRoot` — reads the target's
   VSpaceRoot object.
2. `root.lookup addr` — traverses the VSpaceRoot's `mappings`
   RHTable.

Both are reads (no writes to the VSpaceRoot itself), so a read lock
on the target's VSpaceRoot is sufficient.  Without this lock, the
IPC-buffer validation could race with a concurrent
`VSpaceMap`/`VSpaceUnmap` on the same address space and observe an
inconsistent mapping.

The caller pre-resolves `targetTcb.vspaceRoot`:

```
let vsr := (s.getTcb? targetTcbTid).map (·.vspaceRoot)
```

`vsr = none` covers the case where the target TCB itself doesn't
exist; in that case the syscall fails before reaching
`setIPCBufferOp` and no VSpace read happens. -/
def lockSet_tcbSetIPCBuffer (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (targetTcbTid : ThreadId)
    (targetVSpaceRootObjId : Option ObjId)
    (queueOwner : Option QueueOwner) : LockSet :=
  lockSetExtendOpt
    (lockSetExtendOpt
      (lockSetOfList
        [(tcbLock callerTid, .read),
         (cnodeLock cnodeRootObjId, .read),
         (tcbLock targetTcbTid, .write)])
      (targetVSpaceRootObjId.map (fun vsr => (vspaceRootLock vsr, .read))))
    (queueOwnerMember queueOwner)

/-- WS-SM SM5.H.4: `lockSet` for `tcbSetAffinity`.

`setThreadCpuAffinityOp` writes the target TCB's `cpuAffinity` field (covered by
`tcbLock targetTcbTid .write` in the base) and, for a SchedContext-bound target,
migrates that SchedContext's pending replenishments to the new home core.  The
replenishment migration relocates entries between the source/destination
*replenish-queue* slots (SchedulerState fields, in SM5.A's separate `SchedLockId`
domain), but the bound SchedContext is included here as a `write` for the
conservative kernel-object footprint — matching `lockSet_tcbSetPriority`'s shape.

The caller pre-resolves `targetTcb.schedContextBinding.scId?` identically to
`lockSet_tcbSetPriority`; `boundSchedContextId = none` covers the unbound target
(no replenishments to migrate). -/
def lockSet_tcbSetAffinity (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (targetTcbTid : ThreadId)
    (boundSchedContextId : Option SchedContextId)
    (queueOwner : Option QueueOwner) : LockSet :=
  lockSetExtendOpt
    (lockSetExtendOpt
      (lockSetOfList
        [(tcbLock callerTid, .read),
         (cnodeLock cnodeRootObjId, .read),
         (tcbLock targetTcbTid, .write)])
      (boundSchedContextId.map (fun sc => (schedContextLock sc, .write))))
    (queueOwnerMember queueOwner)

/-- PR #887 review: `lockSet` for `tcbSetFaultHandler`.

`setThreadFaultHandlerOp` writes the target TCB's `faultHandler` field (covered
by `tcbLock targetTcbTid .write`) after validating the candidate CPtr through
the **target's** CSpace root — a read walk of that CNode
(`resolveFaultHandlerCPtr`), which is the fourth lock.  The caller pre-resolves
`(s.getTcb? targetTcbTid).map (·.cspaceRoot)`; `none` covers a missing target
(the syscall fails before any CNode is read), and a caller whose own root *is*
the target's passes `none` too, since that read lock is already in the base.

**The validated endpoint is the fifth lock** (PR #887 review round 3).  The
same resolution reads `st.getEndpoint? epId` to check that the capability the
CPtr names is an endpoint before the CPtr is stored — the kind check
`serviceRegister` locks its endpoint for (audit-pass-6), and for the same
reason: without it a concurrent endpoint retype has no conflicting lock and
races the check, so a handler could be recorded from a state that was never
coherently validated.  The caller pre-resolves the capability's target the way
`resolveFaultHandlerCPtr` does — the slot `resolveCapAddress` names through the
target's root, its capability's `.object` target — and passes that `ObjId`;
`none` when the walk fails or the target is not an object, since the operation
then refuses before reading any endpoint.  Read mode, as the operation never
writes the endpoint.  This footprint names the walk's **root** and nothing
below it, which WS-RR RR7.41 proved is the *complete* CNode footprint of every
resolution the live seam admits: `abiEntryGate` accepts only a single-level
resolution, and `Capability.cspaceWalkPath_single_level` says such a walk reads
exactly its root.  A multi-level walk — for which a root-only footprint would be
false — is refused there, so no footprint is declared for one; a future consumer
that wants to admit one takes `Capability.cspaceWalkLockSet` through
`declaredLockSetForCSpaceWalk` — which refuses a walk wider than
`maxLockSetSize` rather than declaring past the bound, and names the key a
failed lookup read (PR #892 review round 4) — and whose conflict against an
interior `cspaceDelete` is `cspaceWalk_conflicts_with_delete`. -/
def lockSet_tcbSetFaultHandler (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (targetTcbTid : ThreadId)
    (targetCnodeRootObjId : Option ObjId) (handlerEndpointObjId : Option ObjId)
    (queueOwner : Option QueueOwner) : LockSet :=
  lockSetExtendOpt
    (lockSetExtendOpt
      (lockSetExtendOpt
        (lockSetOfList
          [(tcbLock callerTid, .read),
           (cnodeLock cnodeRootObjId, .read),
           (tcbLock targetTcbTid, .write)])
        (targetCnodeRootObjId.map (fun cn => (cnodeLock cn, .read))))
      (handlerEndpointObjId.map (fun ep => (endpointLock ep, .read))))
    (queueOwnerMember queueOwner)

-- ============================================================================
-- SM3.B.3 (audit-pass-5) — PIP-chain-walk start markers
-- ============================================================================

/-! ## Dynamic priority-inheritance chain locking

Three user syscalls (`.call`, `.reply`, `.replyRecv`) invoke a
priority-inheritance chain walk after their core IPC mutation
completes:

* `endpointCallWithDonation`: calls `propagatePriorityInheritance
  receiverTid` on the handshake path (only when the endpoint had a
  blocked receiver waiting at call-time).
* `endpointReplyWithDonation`: calls `revertPriorityInheritance
  callerTid` after the base reply.
* `endpointReplyRecvWithDonation`: calls `revertPriorityInheritance
  callerTid` after the base replyRecv.

The chain walk visits each TCB in the blocking graph reachable from
the start point via the `blockingServer` relation, updating each
visited TCB's `pipBoost` field.  The **chain length is
state-discovered** — it depends on the current blocking graph
topology, which cannot be statically pre-resolved from syscall args.

Plan §4.1 acknowledges this case as "variable number of locks" and
permits dynamic acquisition under the SM0.I hierarchy/ObjId total
order discipline.  The plan's static lockSet contract
(`Args → Finset (LockId × AccessMode)`) cannot include the chain
TCBs in its result; instead, we **expose the chain start point**
as a separate hint via the `pipChainStart_<τ>` family below.

### Contract for SM3.C consumers

If `pipChainStart_<τ> args = some startTid`, then the kernel
transition `<τ>` will invoke a PIP chain walk starting at
`startTid` **after** the static-lockSet action completes.  SM3.C
**must**:

1. Acquire the static `lockSet_<τ> args` first.  For the three
   IPC markers the static set happens to include `startTid`
   itself (the chain start is the receiver/caller, already a
   static-footprint member); for `pipChainStart_tcbSuspend`
   (SM6.E) the chain start is the victim's captured upstream
   blocking server, which is NOT in `lockSet_tcbSuspend` — the
   walker's first CAS-acquisition covers it (the SM3.C.11 walk
   path includes `startTid`; `PipChainPath.singleton`).
   Deadlock-freedom never rested on static inclusion: dynamic
   chain locks are try-acquired (CAS) under bounded retries, so
   the walker never hold-and-waits (SM3.C.11.a strategy step 4).
2. After the core action mutates state, invoke a dynamic
   chain-walk locking strategy starting at `startTid`.  The walk
   must:
   - Read the next chain link (`blockingServer`) under at least
     the current TCB's read lock.
   - Acquire the next chain TCB's lock in **`ObjId.val` ascending
     order** to preserve the SM0.I total order on
     `LockKind.tcb`-level locks (deadlock-freedom obligation).
   - Update `pipBoost` under the chain TCB's write lock, AND —
     WS-SM SM6.E (PR #831 review 3) — hold the member's home-core
     `SchedLockId.runQueue` **write** lock for the same step: the
     per-core boost (`updatePipBoostOnCore`, reached via
     `pipBoostWithWake` / `propagatePipChainCrossCore`) re-buckets
     the member's run queue on **its** home core, a
     scheduler-domain write no static footprint can enumerate
     (the chain is state-discovered).  Both locks are CAS-try
     acquisitions under the bounded-retry budget, so the
     hold-and-wait-free deadlock argument is unchanged.
3. Release in reverse order.

If `pipChainStart_<τ> args = none`, no chain walk is invoked by
`<τ>`; SM3.C's standard `withLockSet` suffices.

### Why a separate function (not a lockSet field)

Plan §4.1's `lockSet : args → Finset` signature is preserved
unchanged.  The chain-start hint is structural metadata about the
transition (a "follow this dynamic obligation" signal), not a
lockSet element.  Separating the two:

* Keeps `lockSet` honest: it declares exactly the static locks.
* Surfaces the dynamic obligation explicitly at the type level
  (SM3.C cannot forget to handle the chain).
* Allows SM3.C to use different dynamic strategies (optimistic
  walk + verify, lock-coupling, coarse PIP-graph lock) without
  changing `lockSet`'s signature.

Detailed dynamic-walk design lives in SM3.C.11 (see
`SMP_PER_OBJECT_LOCKS_PLAN.md` §5.3).
-/

/-- WS-SM SM3.B.3 audit-pass-5: chain-start hint for `.call`.

`endpointCallWithDonation` invokes `propagatePriorityInheritance
receiverTid` **only on the handshake path** (when the endpoint had
a blocked receiver at call-time).  When `receiverTid = none` the
caller blocks waiting, and no chain walk is invoked.  So the
chain-start signal mirrors the `receiverTid` argument exactly. -/
@[inline] def pipChainStart_endpointCall
    (_callerTid : ThreadId) (_cnodeRootObjId _endpointObjId : ObjId)
    (receiverTid : Option ThreadId)
    (_donatedScId : Option SchedContextId) : Option ThreadId :=
  receiverTid

/-- WS-SM SM3.B.3 audit-pass-5: chain-start hint for `.reply`.

`endpointReplyWithDonation` unconditionally invokes
`revertPriorityInheritance callerTid` after the core reply
succeeds (regardless of whether `applyReplyDonation` actually
returned a SC).  The chain walks upward from the replier (=caller)
through the replier's `blockingServer` graph; in the common case
the replier is no longer blocked (just replied), so the chain
length is 1 (`updatePipBoost callerTid` only, no recursion).  In
edge cases where the replier is itself blocked, the chain extends. -/
@[inline] def pipChainStart_endpointReply
    (callerTid : ThreadId) (_cnodeRootObjId : ObjId)
    (_replyTargetTid : ThreadId)
    (_donatedScId : Option SchedContextId)
    (_donatedOriginalOwnerTid : Option ThreadId) : Option ThreadId :=
  some callerTid

/-- WS-SM SM3.B.3 audit-pass-5: chain-start hint for `.replyRecv`.

`endpointReplyRecvWithDonation` invokes
`revertPriorityInheritance callerTid` (== the receiver, who's
also the replier in the combined transition) after the base
replyRecv succeeds.  Symmetric to `pipChainStart_endpointReply`. -/
@[inline] def pipChainStart_replyRecv
    (callerTid : ThreadId) (_cnodeRootObjId : ObjId)
    (_replyTargetTid : ThreadId) (_endpointObjId : ObjId)
    (_newSenderTid : Option ThreadId)
    (_donatedScId : Option SchedContextId)
    (_donatedOriginalOwnerTid : Option ThreadId) : Option ThreadId :=
  some callerTid

/-- WS-SM SM6.E (suspend PIP-revert ordering fix): chain-start hint for
`.tcbSuspend`.

`suspendThread` / `suspendThreadOnCore` invoke the PIP revert walk from the
victim's **captured upstream blocking server** — the D4-N
capture → clear → revert-from-server order (`timeoutThread`'s discipline):
the reply-blocking edge is read at G2-precapture, `cancelIpcBlocking` clears
the victim's `ipcState`, and the walk then recomputes each chain member's
`pipBoost` from the post-teardown `waitersOf` (which no longer includes the
victim), genuinely dropping the victim's donation.  A victim that was not
reply-blocked at entry (`blockingServer` = `none`) triggers no walk.  So the
chain-start signal is exactly the captured server. -/
@[inline] def pipChainStart_tcbSuspend
    (_victimTid : ThreadId)
    (capturedBlockingServer : Option ThreadId) : Option ThreadId :=
  capturedBlockingServer

-- ============================================================================
-- SM3.B.4 — permittedKinds and lockSet_consistent
-- ============================================================================

/-- WS-SM SM3.B.4: per-transition set of permitted `LockKind`s.

A transition's lock-set may only contain LockIds whose kind is in
this set.  The `lockSet_consistent` theorem (SM3.B.4) discharges
this for every declared `lockSet_<τ>`.

Returns the list of kinds that *could* appear in the transition's
lockSet (over all argument values, including all possible
`Option` cases). -/
def permittedKinds (sid : SyscallId) : List LockKind :=
  match sid with
  -- IPC syscalls.  `.call`, `.reply`, `.replyRecv` may traverse a
  -- SchedContext-donation path (per audit-pass-3 extension).
  -- **WS-RR RR7.7**: `.objStore` — a capability-carrying rendezvous installs
  -- into the receiver's CSpace and writes the CDT maps with it, and the CDT
  -- maps are `SystemState`-level structure whose declared subject is
  -- `stateLevelLock` (kind `.objStore`, hierarchy level 0, so it is acquired
  -- first and the by-kind ladder stays acyclic).  `.cnode` was already here
  -- for the caller's root; the receiver's is the same kind in write mode.
  | .send =>
      [.tcb, .cnode, .endpoint, .objStore]
  -- WS-SM SM6.D: `.receive` may link a server-supplied Reply object to a
  -- rendezvousing `Call` caller (`linkCallerReply` writes `reply.caller`), and
  -- `.call` / `.reply` / `.replyRecv` link or consume a Reply — all under the
  -- per-object reply write-lock, so `.reply` enters their permitted kinds.
  -- WS-RR RR7.11: `.objStore` for the reason it joins `.send` and `.call` — the
  -- receive leg installs through the same `ipcTransferSingleCap` and writes the
  -- same CDT maps, whose declared subject is `stateLevelLock`.
  -- **WS-OD OD3.6**: `.schedContext` — a receive that rendezvouses with a queued
  -- `Call` donates the caller's scheduling context to the receiver (seL4-MCS's
  -- `receiveIPC`), so this arm reaches the same donation primitive `.call` does;
  -- and `.objStore` covers that donation's `scThreadIndex` write as well as the
  -- CDT maps.
  | .receive =>
      [.tcb, .cnode, .endpoint, .schedContext, .reply, .objStore]
  -- WS-RR RR7.7: `.objStore` for the same reason it joins `.send` — a Call
  -- that carries capabilities writes the CDT maps.
  | .call =>
      [.tcb, .cnode, .endpoint, .schedContext, .reply, .objStore]
  -- **WS-OD OD3.5**: `.objStore` — the donation return
  -- (`returnDonatedSchedContext`) writes `SystemState.scThreadIndex`, and that
  -- field is an `RHTable`, so an insert may rehash and back-shift the whole
  -- table.  It does not decompose by object, which is the same reason the CDT
  -- maps take this lock (RR7.9/RR7.11), so the declared subject is
  -- `stateLevelLock`.  Level 0, acquired first, ladder unaffected.
  | .reply =>
      [.tcb, .cnode, .schedContext, .reply, .objStore]
  -- WS-RR RR7.11: `.objStore` for the same reason — this arm's receive leg is
  -- the WithCaps receive.
  | .replyRecv =>
      [.tcb, .cnode, .endpoint, .schedContext, .reply, .objStore]
  -- Notification syscalls.  `.notificationSignal` may take the seL4 bound-delivery
  -- path (WS-SM SM6.B): a signal to a notification whose bound TCB is
  -- `BlockedOnReceive` dequeues that TCB from its endpoint and writes it, so the
  -- footprint additionally covers an `.endpoint` lock (the bound TCB's endpoint).
  -- `.endpoint` already coexists with `.notification` in `.tcbSuspend`, so the
  -- by-kind lock ladder stays acyclic.
  | .notificationSignal =>
      [.tcb, .cnode, .notification, .endpoint]
  | .notificationWait =>
      [.tcb, .cnode, .notification]
  -- Capability syscalls.  `.mintReplyCap` (PR #822 Phase H) derives a `.replyCap`
  -- from an `.object`-to-Reply cap into a CNode slot — same CNode/TCB footprint as
  -- the other cap-insert ops (it does not write the Reply object itself).
  -- WS-RR RR7.9: `.objStore` — all four write the CDT (three mint nodes and add
  -- an edge, the delete removes one), and the CDT is `SystemState`-level
  -- structure whose declared subject is `stateLevelLock`.  Level 0, so it is
  -- acquired first and the by-kind ladder stays acyclic.
  | .cspaceMint | .cspaceCopy | .cspaceMove | .cspaceDelete | .mintReplyCap =>
      [.tcb, .cnode, .objStore]
  -- Lifecycle.  **Every kind, for the reason `.declassify` admits every kind**
  -- (PR #873 round 7): SM9.D.12 makes the retype the arm that *clears*
  -- provenance at `args.targetObj`, so `lockSet_lifecycleRetype` carries that
  -- target's own lock — and the decoded target's type is whatever the state
  -- says, since a retype re-purposes an object of any kind.  The fixed part
  -- stays pinned by `lockSet_lifecycleRetype_nonTarget_kinds`, and the by-kind
  -- ladder is unaffected (acquisition order is `LockKind.level`, a total order
  -- over all ten kinds, so a wider admission cannot introduce a cycle).
  | .lifecycleRetype =>
      [.tcb, .cnode, .untyped,
       .objStore, .endpoint, .notification, .reply, .schedContext, .vspaceRoot, .page]
  -- VSpace syscalls
  -- `.vspaceUnifyInstruction` (SM7.D) shares the footprint but takes the
  -- VSpaceRoot in read mode: it modifies no page table, only cache state.
  | .vspaceMap | .vspaceUnmap | .vspaceUnifyInstruction =>
      [.tcb, .cnode, .vspaceRoot]
  -- WS-SM SM8.C.9: `.declassify` reads the caller TCB (to resolve the running
  -- subject's domain) and the caller's CNode (capability resolution), and its
  -- only state-level write is `SystemState.declassificationAuditLog` —
  -- declared since PR #870 round 7 through the `.objStore` singleton
  -- (`stateLevelLock`, write mode): the trail append must exclude against a
  -- concurrent `.auditDrain`'s read-modify-write.
  --
  -- **And every remaining kind, because the target can be any object.**  The
  -- live arm takes `cap.target = .object targetId` and hands that id to
  -- `declassifyObjectFromCore`, which commits a `storeObject` at it; nothing
  -- narrows the object's *type*.  SM9.D.17 then gave `lockSet_declassify` a
  -- `targetLock : Option LockId` for the origination key, and a `LockId` is
  -- `⟨kind, objId⟩` with the kind read off the state — so a downgrade of an
  -- endpoint, a notification, a reply, a scheduling context, a VSpace root, an
  -- untyped region or a page frame contributes that kind to the resolved
  -- footprint.  Listing only `[.tcb, .cnode, .objStore]` (PR #873 round 6) made
  -- `lockSet_consistent_declassify` provable *only* at the default `none`,
  -- while `permittedKinds`' own contract is "over all argument values,
  -- including all possible `Option` cases" — so the resolved footprint could
  -- carry a kind the inventory downstream deadlock and consistency reasoning
  -- reads did not admit.
  --
  -- Admitting every kind is honest rather than lax: what keeps this arm pinned
  -- is `lockSet_declassify_nonTarget_kinds`, which holds the three members the
  -- transition itself takes to exactly `[.tcb, .cnode, .objStore]`, so drift in
  -- the *fixed* part is still a failure.  The by-kind ladder is unaffected —
  -- acquisition order is by `LockKind.level`, which is a total order over all
  -- ten kinds, so admitting more kinds cannot introduce a cycle.
  | .declassify =>
      [.tcb, .cnode, .objStore,
       .untyped, .endpoint, .notification, .reply, .schedContext, .vspaceRoot, .page]
  -- WS-SM SM9.C.8: `.declassifySignal` is the *data-carrying* declassification —
  -- the ordinary `.notificationSignal` (whose kinds it inherits wholesale,
  -- bound-delivery `.endpoint` included) plus the trail append `.declassify`
  -- performs, hence the `.objStore` singleton.  The union is deliberate rather
  -- than a fresh list: the transition really does both, so listing fewer kinds
  -- than either half would under-declare a write the dispatch commits.
  | .declassifySignal =>
      [.tcb, .cnode, .notification, .endpoint, .objStore]
  -- WS-SM SM9.A.12: the audit reader and the drain read the caller TCB (for the
  -- reader's clearance) and the caller's CNode (capability resolution), and
  -- touch only `SystemState` fields — the trail and its epoch — which is
  -- exactly why they carry the `.objStore` singleton (PR #870 round 7): read
  -- mode at the reader, write mode at the drain, the shared-state
  -- serialization no per-object kind can express.
  | .auditRead | .auditDrain =>
      [.tcb, .cnode, .objStore]
  -- Service syscalls.  `.serviceRegister` reads `st.objects[epId]?`
  -- (audit-pass-6 extension); the other two only touch `serviceRegistry`.
  -- WS-RR RR7.23: `.objStore` on all three — `serviceRegistry` is a
  -- `SystemState`-level map, exactly like the audit trail, and the member that
  -- serialises it is `stateLevelLock` (kind `.objStore`, hierarchy level 0, so
  -- it is acquired first and the by-kind ladder stays acyclic).
  | .serviceRegister =>
      [.tcb, .cnode, .endpoint, .objStore]
  | .serviceRevoke | .serviceQuery =>
      [.tcb, .cnode, .objStore]
  -- **WS-RR RR7.38 — `.endpoint` and `.notification` on every arm that can
  -- write a *queued* TCB.**  Splicing a blocked thread out of its wait queue
  -- writes its neighbours' link fields, TCBs the splice holds no `tcbLock` for.
  -- Those writes are authorized by the queue owner's write lock
  -- (`suspendFootprint_splice_neighbors_under_endpoint_lock`); making them
  -- *excluded* against other writers of the same TCBs needs every footprint
  -- that can target a queued thread to declare the same lock, which is the
  -- `queueOwner` member those footprints now carry.  Its kind is whatever owns
  -- the queue, and `QueueOwner.lock_kind` says that is exactly one of these
  -- two — so this is a two-kind widening rather than the `.declassify`
  -- admit-everything shape.  The by-kind ladder is unaffected for the reason
  -- given there: acquisition order is `LockKind.level`, a total order over all
  -- ten kinds, so a wider admission cannot introduce a cycle.
  -- SchedContext syscalls.  **WS-OD OD3.5**: the bind and the unbind maintain
  -- `SystemState.scThreadIndex` (`scThreadIndexAdd` / `scThreadIndexRemove`),
  -- an `RHTable` whose insert may rehash, so both declare `stateLevelLock`.
  -- `.schedContextConfigure` writes the SchedContext and the bound thread and
  -- touches no index, so it is split out rather than widened with them.
  | .schedContextBind | .schedContextUnbind =>
      [.tcb, .cnode, .schedContext, .endpoint, .notification, .objStore]
  | .schedContextConfigure =>
      [.tcb, .cnode, .schedContext, .endpoint, .notification]
  -- TCB lifecycle/config.  `.tcbSuspend` may traverse a donation
  -- cancellation path (per audit-pass-3 extension).
  -- `.tcbSetPriority` and `.tcbSetMCPriority` write a bound or donated
  -- SchedContext via `updatePrioritySource` (audit-pass-6 extension).
  -- `.tcbSetIPCBuffer` reads the target's VSpaceRoot via
  -- `validateIpcBufferAddress` (audit-pass-6 extension).
  -- WS-SM SM6.E: suspending a `.blockedOnReply` caller consumes its
  -- single-use reply link (`cancelIpcBlocking` → `consumeReplyLink`
  -- writes `reply.caller := none` — the SM6.D reply-object fold), so the
  -- suspend footprint also covers a `.reply` write lock.  Without it the
  -- reply-link teardown would mutate the Reply object outside the
  -- acquired 2PL set, racing a concurrent `.receive`/`.reply` that
  -- holds the same Reply's `replyLock` on another core.
  -- **WS-OD OD3.5**: `.objStore` — a suspend that cancels a donation runs
  -- `cancelDonation` / `returnDonationToCancelledCaller`, both of which
  -- maintain `SystemState.scThreadIndex`; see `.reply` above for why an
  -- `RHTable` write takes the state-level lock.
  | .tcbSuspend =>
      [.tcb, .cnode, .endpoint, .notification, .schedContext, .reply, .objStore]
  | .tcbResume =>
      [.tcb, .cnode, .endpoint, .notification]
  | .tcbSetPriority | .tcbSetMCPriority =>
      [.tcb, .cnode, .schedContext, .endpoint, .notification]
  | .tcbSetIPCBuffer =>
      [.tcb, .cnode, .vspaceRoot, .endpoint, .notification]
  -- WS-SM SM5.H.4: `setThreadCpuAffinityOp` writes the target TCB's `cpuAffinity`
  -- and, for a SchedContext-bound target, migrates that SC's pending replenishments
  -- (so the bound SchedContext object is in the conservative kernel-object footprint;
  -- the run-queue / replenish-queue slots are SM5.A's separate `SchedLockId` domain).
  | .tcbSetAffinity =>
      [.tcb, .cnode, .schedContext, .endpoint, .notification]
  -- PR #887 review: `setThreadFaultHandlerOp` writes the target TCB's
  -- `faultHandler` and reads the target's root CNode to validate the CPtr —
  -- and (review round 3) the endpoint the CPtr names, for the kind check.
  | .tcbSetFaultHandler =>
      [.tcb, .cnode, .endpoint, .notification]
  -- WS-SM SM6.B: bind/unbind a notification to a TCB.  Both the notification
  -- (write — `boundTCB`) and the bound TCB (write — `boundNotification`) are in
  -- the footprint, plus the CNode (read) covering the capability resolution.
  | .tcbBindNotification | .tcbUnbindNotification =>
      [.tcb, .cnode, .notification, .endpoint]

/-- WS-SM SM3.B.4 (PR #873 round 6): **the kind inventory admits any target.**

The honest reading of the widened `permittedKinds .declassify`, as a checked
value rather than as a comment: the arm hands `cap.target = .object targetId`
to a transition that commits a `storeObject` at it, so the target's kind is
whatever the state says and nothing narrows it. -/
theorem permittedKinds_declassify_admits_every_kind (k : LockKind) :
    k ∈ permittedKinds .declassify := by
  cases k <;> decide

/-- WS-SM SM3.B.4 (PR #873 round 7): **and the retype's inventory admits any
re-purposed target**, for the same reason one theorem up — the arm reads
`args.targetObj` from the decoded arguments and re-purposes an object whose kind
the state, not the syscall, decides. -/
theorem permittedKinds_lifecycleRetype_admits_every_kind (k : LockKind) :
    k ∈ permittedKinds .lifecycleRetype := by
  cases k <;> decide

/-- WS-SM SM3.B.4 helper: `Decidable` `kind ∈ permittedKinds τ`. -/
instance (k : LockKind) (sid : SyscallId) :
    Decidable (k ∈ permittedKinds sid) := by
  unfold permittedKinds
  cases sid <;> exact inferInstance

-- ============================================================================
-- SM3.B.4 — generic membership-traces-back theorem for fold-based lockSets
-- ============================================================================

-- `LockSet.insertOrMerge_mem` is defined in `LockSet.lean`; we re-use it
-- here for the fold-based membership trace-back.

/-- **WS-RR RR7.41**: every input key reaches the built set — the forward
direction of `lockSetOfList_mem_inv`.

The mode may have been merged upward by a later duplicate (`AccessMode.lub`), so
the statement is existential in the mode: what a caller needs is that the *key*
is declared, and the mode a merge produces is at least the one it put in.  Needed
by the CSpace-walk footprint, which builds its set from a walked list and must
know every visited CNode is named. -/
theorem lockSetOfList_mem_of_mem (input : List (LockId × AccessMode))
    (l : LockId) (m : AccessMode) (hMem : (l, m) ∈ input) :
    ∃ m', (l, m') ∈ (lockSetOfList input).pairs := by
  -- Strengthened over an arbitrary accumulator: once a key is in the
  -- accumulator it stays, and the fold reaches every input element.
  suffices h : ∀ (suffix : List (LockId × AccessMode)) (acc : LockSet),
      ((l, m) ∈ suffix ∨ (∃ m', (l, m') ∈ acc.pairs)) →
      ∃ m', (l, m') ∈ (suffix.foldl
        (fun a p => a.insertOrMerge p.fst p.snd) acc).pairs by
    exact h input LockSet.empty (Or.inl hMem)
  intro suffix
  induction suffix with
  | nil =>
      intro acc h
      rcases h with hNil | hAcc
      · exact absurd hNil (by simp)
      · exact hAcc
  | cons hd tl ih =>
      intro acc h
      refine ih (acc.insertOrMerge hd.fst hd.snd) ?_
      rcases h with hMemCons | ⟨m', hAcc⟩
      · rcases List.mem_cons.mp hMemCons with hEq | hTl
        · subst hEq
          exact Or.inr (LockSet.mem_insertOrMerge_self acc l m)
        · exact Or.inl hTl
      · by_cases hKey : l = hd.fst
        · subst hKey
          exact Or.inr (LockSet.mem_insertOrMerge_self acc hd.fst hd.snd)
        · exact Or.inr ⟨m',
            LockSet.mem_insertOrMerge_of_mem_of_ne acc hd.fst hd.snd (l, m') hAcc hKey⟩

/-- WS-SM SM3.B.4 helper: an element of `lockSetOfList pairs`'s
underlying list has fst equal to some pair in `pairs`'s fst.

This is the workhorse that drives `lockSet_consistent`: every
`lockSet_<τ>` is a `lockSetOfList` (possibly with optional
`lockSetExtendOpt` extensions), and every element of the
resulting `.pairs` traces back to either an input literal pair or
an `Option`-extended pair. -/
theorem lockSetOfList_mem_inv (input : List (LockId × AccessMode))
    (p : LockId × AccessMode)
    (hMem : p ∈ (lockSetOfList input).pairs) :
    ∃ p' ∈ input, p.fst = p'.fst := by
  -- Strengthen the induction: starting from any initial accumulator, every
  -- element of the result is either from the original accumulator (unchanged)
  -- or has fst matching some element of the suffix being folded.
  have h := lockSetOfList_mem_inv_aux input LockSet.empty p hMem
  rcases h with hNew | hOld
  · exact hNew
  · -- Empty accumulator has no elements.
    exact absurd hOld (by intro h; cases h)
where
  lockSetOfList_mem_inv_aux :
      ∀ (suffix : List (LockId × AccessMode)) (acc : LockSet)
        (p : LockId × AccessMode),
        p ∈ (suffix.foldl (init := acc)
          (fun a q => a.insertOrMerge q.fst q.snd)).pairs →
        (∃ p' ∈ suffix, p.fst = p'.fst) ∨ p ∈ acc.pairs
  | [], acc, p, hMem => Or.inr (by simpa using hMem)
  | (q :: rest), acc, p, hMem => by
      -- Decompose the fold: foldl on (q :: rest) = foldl rest with acc.insertOrMerge q.fst q.snd
      simp only [List.foldl_cons] at hMem
      have hRec := lockSetOfList_mem_inv_aux rest (acc.insertOrMerge q.fst q.snd) p hMem
      rcases hRec with hFromRest | hFromMerge
      · -- p's fst matches some element in rest; lift to (q :: rest).
        left
        obtain ⟨p', hp'Mem, hp'Eq⟩ := hFromRest
        exact ⟨p', List.mem_cons_of_mem _ hp'Mem, hp'Eq⟩
      · -- p ∈ (acc.insertOrMerge q.fst q.snd).pairs; trace back.
        have := LockSet.insertOrMerge_mem acc q.fst q.snd p hFromMerge
        rcases this with hEq | hFst | hOld
        · -- p = (q.fst, q.snd) — i.e., p = q.
          left
          refine ⟨q, List.mem_cons_self, ?_⟩
          rw [hEq]
        · -- p.fst = q.fst (merged with existing); same conclusion.
          left
          exact ⟨q, List.mem_cons_self, hFst⟩
        · right; exact hOld

/-- WS-SM SM3.B.4 helper: `lockSetExtendOpt S none = S`. -/
@[simp] theorem lockSetExtendOpt_none (S : LockSet) :
    lockSetExtendOpt S none = S := rfl

/-- WS-SM SM3.B.4 helper: `lockSetExtendOpt S (some p)` membership
trace-back. -/
theorem lockSetExtendOpt_mem_inv (S : LockSet) (p : Option (LockId × AccessMode))
    (q : LockId × AccessMode)
    (hMem : q ∈ (lockSetExtendOpt S p).pairs) :
    (∃ pp, p = some pp ∧ q.fst = pp.fst) ∨ q ∈ S.pairs := by
  cases p with
  | none =>
      rw [lockSetExtendOpt] at hMem
      right; exact hMem
  | some pp =>
      simp only [lockSetExtendOpt] at hMem
      have := LockSet.insertOrMerge_mem S pp.fst pp.snd q hMem
      rcases this with hEq | hFst | hOld
      · left
        refine ⟨pp, rfl, ?_⟩
        rw [hEq]
      · left; exact ⟨pp, rfl, hFst⟩
      · right; exact hOld

-- ============================================================================
-- SM3.B.4 — lockSet_consistent: generic builder
-- ============================================================================

/-- WS-SM SM3.B.4 generic consistency lemma: a LockSet built by
`lockSetOfList` extended by 0 or more `lockSetExtendOpt` calls
satisfies the kind-in-permitted invariant if both the base list
and every extension pair satisfy it. -/
theorem lockSet_consistent_of_extended_base
    (base : List (LockId × AccessMode))
    (permitted : List LockKind)
    (hBase : ∀ p ∈ base, p.fst.kind ∈ permitted) :
    ∀ p ∈ (lockSetOfList base).pairs, p.fst.kind ∈ permitted := by
  intro p hMem
  have := lockSetOfList_mem_inv base p hMem
  obtain ⟨p', hp'Mem, hp'Eq⟩ := this
  rw [hp'Eq]
  exact hBase p' hp'Mem

/-- WS-SM SM3.B.4 generic consistency lemma: extending a LockSet via
`lockSetExtendOpt` with a kind-permitted optional pair preserves
the kind-in-permitted invariant. -/
theorem lockSet_consistent_extendOpt
    (S : LockSet) (opt : Option (LockId × AccessMode))
    (permitted : List LockKind)
    (hS : ∀ p ∈ S.pairs, p.fst.kind ∈ permitted)
    (hOpt : ∀ pp, opt = some pp → pp.fst.kind ∈ permitted) :
    ∀ p ∈ (lockSetExtendOpt S opt).pairs, p.fst.kind ∈ permitted := by
  intro p hMem
  rcases lockSetExtendOpt_mem_inv S opt p hMem with ⟨pp, hOptEq, hFst⟩ | hBase
  · rw [hFst]
    exact hOpt pp hOptEq
  · exact hS p hBase

/-- WS-SM SM3.B.4 builder: combine `lockSet_consistent_of_extended_base`
with one `lockSet_consistent_extendOpt`. -/
theorem lockSet_consistent_base_plus_opt
    (base : List (LockId × AccessMode))
    (opt : Option (LockId × AccessMode))
    (permitted : List LockKind)
    (hBase : ∀ p ∈ base, p.fst.kind ∈ permitted)
    (hOpt : ∀ pp, opt = some pp → pp.fst.kind ∈ permitted) :
    ∀ p ∈ (lockSetExtendOpt (lockSetOfList base) opt).pairs,
      p.fst.kind ∈ permitted :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_of_extended_base base permitted hBase) hOpt

/-- WS-SM SM3.B.4 builder: combine with two optional extensions. -/
theorem lockSet_consistent_base_plus_two_opts
    (base : List (LockId × AccessMode))
    (opt₁ opt₂ : Option (LockId × AccessMode))
    (permitted : List LockKind)
    (hBase : ∀ p ∈ base, p.fst.kind ∈ permitted)
    (hOpt₁ : ∀ pp, opt₁ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₂ : ∀ pp, opt₂ = some pp → pp.fst.kind ∈ permitted) :
    ∀ p ∈ (lockSetExtendOpt
              (lockSetExtendOpt (lockSetOfList base) opt₁) opt₂).pairs,
      p.fst.kind ∈ permitted :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_base_plus_opt base opt₁ permitted hBase hOpt₁) hOpt₂

/-- WS-SM SM3.B.4 builder (audit-pass-3): combine with three optional
extensions.  Used by `lockSet_consistent_replyRecv` after audit-pass-3
expanded `lockSet_replyRecv` with the `donatedScId` arg. -/
theorem lockSet_consistent_base_plus_three_opts
    (base : List (LockId × AccessMode))
    (opt₁ opt₂ opt₃ : Option (LockId × AccessMode))
    (permitted : List LockKind)
    (hBase : ∀ p ∈ base, p.fst.kind ∈ permitted)
    (hOpt₁ : ∀ pp, opt₁ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₂ : ∀ pp, opt₂ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₃ : ∀ pp, opt₃ = some pp → pp.fst.kind ∈ permitted) :
    ∀ p ∈ (lockSetExtendOpt (lockSetExtendOpt
              (lockSetExtendOpt (lockSetOfList base) opt₁) opt₂) opt₃).pairs,
      p.fst.kind ∈ permitted :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_base_plus_two_opts base opt₁ opt₂ permitted
      hBase hOpt₁ hOpt₂) hOpt₃

/-- WS-SM SM3.B.4 builder (audit-pass-3): combine with four optional
extensions.  Used by `lockSet_consistent_tcbSuspend` after
audit-pass-3 expanded `lockSet_tcbSuspend` with the `bindingScId`
and `donatedOriginalOwnerTid` args. -/
theorem lockSet_consistent_base_plus_four_opts
    (base : List (LockId × AccessMode))
    (opt₁ opt₂ opt₃ opt₄ : Option (LockId × AccessMode))
    (permitted : List LockKind)
    (hBase : ∀ p ∈ base, p.fst.kind ∈ permitted)
    (hOpt₁ : ∀ pp, opt₁ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₂ : ∀ pp, opt₂ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₃ : ∀ pp, opt₃ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₄ : ∀ pp, opt₄ = some pp → pp.fst.kind ∈ permitted) :
    ∀ p ∈ (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
              (lockSetExtendOpt (lockSetOfList base) opt₁) opt₂) opt₃) opt₄).pairs,
      p.fst.kind ∈ permitted :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_base_plus_three_opts base opt₁ opt₂ opt₃ permitted
      hBase hOpt₁ hOpt₂ hOpt₃) hOpt₄

/-- WS-SM SM6.E builder: combine with five optional extensions.  Used by
`lockSet_consistent_tcbSuspend` after SM6.E expanded `lockSet_tcbSuspend`
with the `consumedReplyId` arg (the reply-link teardown write lock). -/
theorem lockSet_consistent_base_plus_five_opts
    (base : List (LockId × AccessMode))
    (opt₁ opt₂ opt₃ opt₄ opt₅ : Option (LockId × AccessMode))
    (permitted : List LockKind)
    (hBase : ∀ p ∈ base, p.fst.kind ∈ permitted)
    (hOpt₁ : ∀ pp, opt₁ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₂ : ∀ pp, opt₂ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₃ : ∀ pp, opt₃ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₄ : ∀ pp, opt₄ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₅ : ∀ pp, opt₅ = some pp → pp.fst.kind ∈ permitted) :
    ∀ p ∈ (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
              (lockSetExtendOpt (lockSetOfList base) opt₁) opt₂) opt₃) opt₄) opt₅).pairs,
      p.fst.kind ∈ permitted :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_base_plus_four_opts base opt₁ opt₂ opt₃ opt₄ permitted
      hBase hOpt₁ hOpt₂ hOpt₃ hOpt₄) hOpt₅

/-- WS-OD OD3.5 builder: six optional extensions — the arity `lockSet_tcbSuspend`
reaches once the donation cancellation's `scThreadIndex` write declares the
state-level lock. -/
theorem lockSet_consistent_base_plus_six_opts
    (base : List (LockId × AccessMode))
    (opt₁ opt₂ opt₃ opt₄ opt₅ opt₆ : Option (LockId × AccessMode))
    (permitted : List LockKind)
    (hBase : ∀ p ∈ base, p.fst.kind ∈ permitted)
    (hOpt₁ : ∀ pp, opt₁ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₂ : ∀ pp, opt₂ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₃ : ∀ pp, opt₃ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₄ : ∀ pp, opt₄ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₅ : ∀ pp, opt₅ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₆ : ∀ pp, opt₆ = some pp → pp.fst.kind ∈ permitted) :
    ∀ p ∈ (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
              (lockSetExtendOpt (lockSetExtendOpt (lockSetOfList base) opt₁) opt₂) opt₃)
              opt₄) opt₅) opt₆).pairs,
      p.fst.kind ∈ permitted :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_base_plus_five_opts base opt₁ opt₂ opt₃ opt₄ opt₅ permitted
      hBase hOpt₁ hOpt₂ hOpt₃ hOpt₄ hOpt₅) hOpt₆

/-- WS-OD OD3.5 builder: seven optional extensions — the arity `lockSet_replyRecv`
reaches once it declares the recorded server's TCB and the second SchedContext
hand-off. -/
theorem lockSet_consistent_base_plus_seven_opts
    (base : List (LockId × AccessMode))
    (opt₁ opt₂ opt₃ opt₄ opt₅ opt₆ opt₇ : Option (LockId × AccessMode))
    (permitted : List LockKind)
    (hBase : ∀ p ∈ base, p.fst.kind ∈ permitted)
    (hOpt₁ : ∀ pp, opt₁ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₂ : ∀ pp, opt₂ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₃ : ∀ pp, opt₃ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₄ : ∀ pp, opt₄ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₅ : ∀ pp, opt₅ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₆ : ∀ pp, opt₆ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₇ : ∀ pp, opt₇ = some pp → pp.fst.kind ∈ permitted) :
    ∀ p ∈ (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
              (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetOfList base)
              opt₁) opt₂) opt₃) opt₄) opt₅) opt₆) opt₇).pairs,
      p.fst.kind ∈ permitted :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_base_plus_six_opts base opt₁ opt₂ opt₃ opt₄ opt₅ opt₆ permitted
      hBase hOpt₁ hOpt₂ hOpt₃ hOpt₄ hOpt₅ hOpt₆) hOpt₇

/-- WS-OD OD1.5 builder: combine with eight optional extensions — the arity the
state-resolved cancellation footprint reaches once the reclaim's abort prefix
declares the holder's endpoint and its two queue neighbours. -/
theorem lockSet_consistent_base_plus_eight_opts
    (base : List (LockId × AccessMode))
    (opt₁ opt₂ opt₃ opt₄ opt₅ opt₆ opt₇ opt₈ : Option (LockId × AccessMode))
    (permitted : List LockKind)
    (hBase : ∀ p ∈ base, p.fst.kind ∈ permitted)
    (hOpt₁ : ∀ pp, opt₁ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₂ : ∀ pp, opt₂ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₃ : ∀ pp, opt₃ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₄ : ∀ pp, opt₄ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₅ : ∀ pp, opt₅ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₆ : ∀ pp, opt₆ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₇ : ∀ pp, opt₇ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₈ : ∀ pp, opt₈ = some pp → pp.fst.kind ∈ permitted) :
    ∀ p ∈ (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
              (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
              (lockSetExtendOpt (lockSetOfList base) opt₁) opt₂) opt₃) opt₄) opt₅)
              opt₆) opt₇) opt₈).pairs,
      p.fst.kind ∈ permitted :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_extendOpt _ _ _
      (lockSet_consistent_extendOpt _ _ _
        (lockSet_consistent_base_plus_five_opts base opt₁ opt₂ opt₃ opt₄ opt₅ permitted
          hBase hOpt₁ hOpt₂ hOpt₃ hOpt₄ hOpt₅) hOpt₆) hOpt₇) hOpt₈

/-- WS-OD OD3.5 builder: nine optional extensions — the arity the state-resolved
cancellation footprint reaches once the donation hand-back's `scThreadIndex`
write declares the state-level lock. -/
theorem lockSet_consistent_base_plus_nine_opts
    (base : List (LockId × AccessMode))
    (opt₁ opt₂ opt₃ opt₄ opt₅ opt₆ opt₇ opt₈ opt₉ : Option (LockId × AccessMode))
    (permitted : List LockKind)
    (hBase : ∀ p ∈ base, p.fst.kind ∈ permitted)
    (hOpt₁ : ∀ pp, opt₁ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₂ : ∀ pp, opt₂ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₃ : ∀ pp, opt₃ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₄ : ∀ pp, opt₄ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₅ : ∀ pp, opt₅ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₆ : ∀ pp, opt₆ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₇ : ∀ pp, opt₇ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₈ : ∀ pp, opt₈ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₉ : ∀ pp, opt₉ = some pp → pp.fst.kind ∈ permitted) :
    ∀ p ∈ (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
              (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
              (lockSetExtendOpt (lockSetOfList base) opt₁) opt₂) opt₃) opt₄) opt₅)
              opt₆) opt₇) opt₈) opt₉).pairs,
      p.fst.kind ∈ permitted :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_base_plus_eight_opts base opt₁ opt₂ opt₃ opt₄ opt₅ opt₆ opt₇ opt₈
      permitted hBase hOpt₁ hOpt₂ hOpt₃ hOpt₄ hOpt₅ hOpt₆ hOpt₇ hOpt₈) hOpt₉

/-- WS-OD OD3.7: ten optionals — the cancellation footprint's arity once the two
below-head reads join it. -/
theorem lockSet_consistent_base_plus_ten_opts
    (base : List (LockId × AccessMode))
    (opt₁ opt₂ opt₃ opt₄ opt₅ opt₆ opt₇ opt₈ opt₉ opt₁₀ : Option (LockId × AccessMode))
    (permitted : List LockKind)
    (hBase : ∀ p ∈ base, p.fst.kind ∈ permitted)
    (hOpt₁ : ∀ pp, opt₁ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₂ : ∀ pp, opt₂ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₃ : ∀ pp, opt₃ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₄ : ∀ pp, opt₄ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₅ : ∀ pp, opt₅ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₆ : ∀ pp, opt₆ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₇ : ∀ pp, opt₇ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₈ : ∀ pp, opt₈ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₉ : ∀ pp, opt₉ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₁₀ : ∀ pp, opt₁₀ = some pp → pp.fst.kind ∈ permitted) :
    ∀ p ∈ (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
              (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
              (lockSetExtendOpt (lockSetExtendOpt (lockSetOfList base) opt₁) opt₂) opt₃) opt₄)
              opt₅) opt₆) opt₇) opt₈) opt₉) opt₁₀).pairs,
      p.fst.kind ∈ permitted :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_base_plus_nine_opts base opt₁ opt₂ opt₃ opt₄ opt₅ opt₆ opt₇ opt₈ opt₉
      permitted hBase hOpt₁ hOpt₂ hOpt₃ hOpt₄ hOpt₅ hOpt₆ hOpt₇ hOpt₈ hOpt₉) hOpt₁₀

/-- WS-OD OD3.7: eleven optionals — the arity `lockSet_cancelIpcBlocking` reaches
once the reclaim's two below-head reads are declared. -/
theorem lockSet_consistent_base_plus_eleven_opts
    (base : List (LockId × AccessMode))
    (opt₁ opt₂ opt₃ opt₄ opt₅ opt₆ opt₇ opt₈ opt₉ opt₁₀ opt₁₁ : Option (LockId × AccessMode))
    (permitted : List LockKind)
    (hBase : ∀ p ∈ base, p.fst.kind ∈ permitted)
    (hOpt₁ : ∀ pp, opt₁ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₂ : ∀ pp, opt₂ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₃ : ∀ pp, opt₃ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₄ : ∀ pp, opt₄ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₅ : ∀ pp, opt₅ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₆ : ∀ pp, opt₆ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₇ : ∀ pp, opt₇ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₈ : ∀ pp, opt₈ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₉ : ∀ pp, opt₉ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₁₀ : ∀ pp, opt₁₀ = some pp → pp.fst.kind ∈ permitted)
    (hOpt₁₁ : ∀ pp, opt₁₁ = some pp → pp.fst.kind ∈ permitted) :
    ∀ p ∈ (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
              (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
              (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetOfList base)
              opt₁) opt₂) opt₃) opt₄) opt₅) opt₆) opt₇) opt₈) opt₉) opt₁₀) opt₁₁).pairs,
      p.fst.kind ∈ permitted :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_base_plus_ten_opts base opt₁ opt₂ opt₃ opt₄ opt₅ opt₆ opt₇ opt₈ opt₉
      opt₁₀ permitted hBase hOpt₁ hOpt₂ hOpt₃ hOpt₄ hOpt₅ hOpt₆ hOpt₇ hOpt₈ hOpt₉ hOpt₁₀) hOpt₁₁

-- ============================================================================
-- SM3.B.4 — lockSet_consistent per-transition theorems
-- ============================================================================

/-- WS-SM SM3.B.4 helper: TCB lock kinds are `.tcb`. -/
@[simp] theorem tcbLock_kind (tid : ThreadId) : (tcbLock tid).kind = .tcb := rfl

/-- WS-SM SM3.B.4 helper: CNode lock kinds are `.cnode`. -/
@[simp] theorem cnodeLock_kind (oid : ObjId) : (cnodeLock oid).kind = .cnode := rfl

/-- WS-SM SM3.B.4 helper: Endpoint lock kinds are `.endpoint`. -/
@[simp] theorem endpointLock_kind (oid : ObjId) : (endpointLock oid).kind = .endpoint :=
  rfl

/-- WS-SM SM3.B.4 helper: Notification lock kinds are `.notification`. -/
@[simp] theorem notificationLock_kind (oid : ObjId) :
    (notificationLock oid).kind = .notification := rfl

/-- WS-SM SM3.B.4 helper: SchedContext lock kinds are `.schedContext`. -/
@[simp] theorem schedContextLock_kind (scid : SchedContextId) :
    (schedContextLock scid).kind = .schedContext := rfl

/-- WS-SM SM6.D helper: Reply lock kinds are `.reply`. -/
@[simp] theorem replyLock_kind (rid : ReplyId) :
    (replyLock rid).kind = .reply := rfl

/-- WS-SM SM3.B.4 helper: VSpaceRoot lock kinds are `.vspaceRoot`. -/
@[simp] theorem vspaceRootLock_kind (oid : ObjId) :
    (vspaceRootLock oid).kind = .vspaceRoot := rfl

/-- WS-SM SM3.B.4 helper: Untyped lock kinds are `.untyped`. -/
@[simp] theorem untypedLock_kind (oid : ObjId) : (untypedLock oid).kind = .untyped :=
  rfl

-- Audit-pass-1 refactor: the per-transition `lockSet_consistent_*`
-- proofs use a uniform `simp; decide` pattern (where `simp`
-- normalizes `(<lockBuilder> arg).kind` to its concrete `LockKind`
-- via the `@[simp]` `*Lock_kind` lemmas above, then `decide`
-- discharges the `LockKind ∈ permittedKinds <τ>` finite-list
-- membership).  Removed the explicit `simp only [...]` argument list
-- (which forced an `unusedSimpArgs` linter override) — plain `simp`
-- with the `@[simp]`-tagged helpers is sufficient and warning-free.

/-- WS-SM SM3.B.4 (plan §5.2.SM3.B.4) for `.send`: every declared lock
has kind in `permittedKinds .send`.

**WS-RR RR7.7**: stated over **every** `destCnode`, not only the capless
default.  Leaving it partially applied is the same defect the round-6
`.declassify` and round-8 `.receive` fixes closed — a consistency claim
checked against one argument value while a fine-lock consumer acquires the
footprint carrying the other. -/
theorem lockSet_consistent_send (callerTid : ThreadId)
    (cnRoot epId : ObjId) (rTid : Option ThreadId)
    (destCnode : Option ObjId := none)
    -- **WS-OD OD3.11**: stated at the queue-structure-neighbour arity.
    (queueNeighbour : Option ThreadId := none) :
    ∀ p ∈ (lockSet_endpointSend callerTid cnRoot epId rTid destCnode
             queueNeighbour).pairs,
      p.fst.kind ∈ permittedKinds .send :=
  lockSet_consistent_base_plus_four_opts _ _ _ _ _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))
    (by intro pp hpp
        cases rTid with
        | none => simp at hpp
        | some rt => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases destCnode with
        | none => simp at hpp
        | some r => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases destCnode with
        | none => simp at hpp
        | some _ => simp at hpp; rw [← hpp]; simp [stateLevelLock]; decide)
    (by intro pp hpp
        cases queueNeighbour with
        | none => simp at hpp
        | some q => simp at hpp; rw [← hpp]; simp; decide)

/-- WS-SM SM3.B.4 for `.receive`.

PR #873 round 8: stated over **every** `installsCaps`, not only the default.
Leaving it at the default would repeat the round-6 `.declassify` error — a
consistency claim checked against one of the argument values while the resolved
footprint a fine-lock consumer acquires carries the other. -/
theorem lockSet_consistent_receive (callerTid : ThreadId)
    (cnRoot epId : ObjId) (sTid : Option ThreadId)
    (replyId : Option ReplyId := none) (installsCaps : Bool := false)
    (donatedScId : Option SchedContextId) :
    ∀ p ∈ (lockSet_endpointReceive callerTid cnRoot epId sTid replyId installsCaps
             donatedScId).pairs,
      p.fst.kind ∈ permittedKinds .receive :=
  lockSet_consistent_base_plus_four_opts _ _ _ _ _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; cases installsCaps <;> simp <;> decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))
    (by intro pp hpp
        cases sTid with
        | none => simp at hpp
        | some st => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases replyId with
        | none => simp at hpp
        | some rid => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases donatedScId with
        | none => simp at hpp
        | some sc => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases installsCaps with
        | false =>
          cases donatedScId with
          | none => simp at hpp
          | some _ => simp at hpp; rw [← hpp]; simp [stateLevelLock]; decide
        | true => simp at hpp; rw [← hpp]; simp [stateLevelLock]; decide)

/-- WS-SM SM3.B.4 for `.call` (audit-pass-3: donation extension).

**WS-RR RR7.7**: stated over **every** `destCnode`, for the reason
`lockSet_consistent_send` states. -/
theorem lockSet_consistent_call (callerTid : ThreadId)
    (cnRoot epId : ObjId) (rTid : Option ThreadId)
    (donatedScId : Option SchedContextId)
    (replyId : Option ReplyId := none)
    (destCnode : Option ObjId := none)
    -- **WS-OD OD3.11**: stated at the queue-structure-neighbour arity.
    (queueNeighbour : Option ThreadId := none) :
    ∀ p ∈ (lockSet_endpointCall callerTid cnRoot epId rTid donatedScId replyId
             destCnode queueNeighbour).pairs,
      p.fst.kind ∈ permittedKinds .call :=
  lockSet_consistent_base_plus_six_opts _ _ _ _ _ _ _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))
    (by intro pp hpp
        cases rTid with
        | none => simp at hpp
        | some rt => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases donatedScId with
        | none => simp at hpp
        | some sc => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases replyId with
        | none => simp at hpp
        | some rid => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases destCnode with
        | none => simp at hpp
        | some r => simp at hpp; rw [← hpp]; simp; decide)
    -- WS-OD OD3.5: the state-level member now fires on the transfer *or* the
    -- donation, so the obligation is discharged from the `if` rather than from
    -- one optional's `some`.
    (by intro pp hpp
        by_cases hc : destCnode.isSome || donatedScId.isSome
        · rw [if_pos hc] at hpp
          simp at hpp; rw [← hpp]; simp [stateLevelLock]; decide
        · rw [if_neg hc] at hpp; simp at hpp)
    (by intro pp hpp
        cases queueNeighbour with
        | none => simp at hpp
        | some q => simp at hpp; rw [← hpp]; simp; decide)

/-- WS-SM SM3.B.4 for `.reply` (audit-pass-3 + audit-pass-4: donation-
return extension with separate `donatedOriginalOwnerTid` arg). -/
theorem lockSet_consistent_reply (callerTid : ThreadId)
    (cnRoot : ObjId) (rTid : ThreadId)
    (donatedScId : Option SchedContextId)
    (donatedOriginalOwnerTid : Option ThreadId)
    (replyId : Option ReplyId := none)
    (belowHeadReplyId : Option ReplyId) (outerCallerTid : Option ThreadId) :
    ∀ p ∈ (lockSet_endpointReply callerTid cnRoot rTid donatedScId
              donatedOriginalOwnerTid replyId belowHeadReplyId outerCallerTid).pairs,
      p.fst.kind ∈ permittedKinds .reply :=
  lockSet_consistent_base_plus_six_opts _ _ _ _ _ _ _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))
    (by intro pp hpp
        cases donatedScId with
        | none => simp at hpp
        | some sc => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases donatedOriginalOwnerTid with
        | none => simp at hpp
        | some ot => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases replyId with
        | none => simp at hpp
        | some rid => simp at hpp; rw [← hpp]; simp; decide)
    -- WS-OD OD3.7: the Reply below the stack head, read to find the outer
    -- caller — a `.reply` kind, which this arm already admits.
    (by intro pp hpp
        cases belowHeadReplyId with
        | none => simp at hpp
        | some rid => simp at hpp; rw [← hpp]; simp; decide)
    -- WS-OD OD3.7: …and that caller's own TCB, read to validate it.
    (by intro pp hpp
        cases outerCallerTid with
        | none => simp at hpp
        | some ot => simp at hpp; rw [← hpp]; simp; decide)
    -- WS-OD OD3.5: the donation return's `scThreadIndex` write.
    (by intro pp hpp
        cases donatedScId with
        | none => simp at hpp
        | some _ => simp at hpp; rw [← hpp]; simp [stateLevelLock]; decide)

/-- WS-SM SM3.B.4 for `.replyRecv` (audit-pass-3 + audit-pass-4:
donation-return extension with separate `donatedOriginalOwnerTid`
arg).  **WS-OD OD3.5**: seven optionals — the recorded server's TCB and the
second SchedContext hand-off join the five it already carried. -/
theorem lockSet_consistent_replyRecv (callerTid : ThreadId)
    (cnRoot : ObjId) (rTid : ThreadId) (epId : ObjId)
    (newSenderTid : Option ThreadId)
    (donatedScId : Option SchedContextId)
    (donatedOriginalOwnerTid : Option ThreadId)
    (replyId : Option ReplyId := none) (installsCaps : Bool := false)
    (donationServerTid : Option ThreadId) (redonatedScId : Option SchedContextId)
    (belowHeadReplyId : Option ReplyId) (outerCallerTid : Option ThreadId) :
    ∀ p ∈ (lockSet_replyRecv callerTid cnRoot rTid epId newSenderTid
              donatedScId donatedOriginalOwnerTid replyId installsCaps
              donationServerTid redonatedScId belowHeadReplyId outerCallerTid).pairs,
      p.fst.kind ∈ permittedKinds .replyRecv :=
  lockSet_consistent_base_plus_nine_opts _ _ _ _ _ _ _ _ _ _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; cases installsCaps <;> simp <;> decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))
    (by intro pp hpp
        cases newSenderTid with
        | none => simp at hpp
        | some st => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases donatedScId with
        | none => simp at hpp
        | some sc => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases donatedOriginalOwnerTid with
        | none => simp at hpp
        | some ot => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases replyId with
        | none => simp at hpp
        | some rid => simp at hpp; rw [← hpp]; simp; decide)
    -- WS-OD OD3.5: the recorded server's TCB…
    (by intro pp hpp
        cases donationServerTid with
        | none => simp at hpp
        | some srv => simp at hpp; rw [← hpp]; simp; decide)
    -- …the second hand-off's SchedContext…
    (by intro pp hpp
        cases redonatedScId with
        | none => simp at hpp
        | some sc => simp at hpp; rw [← hpp]; simp; decide)
    -- …WS-OD OD3.7's two below-head reads — the Reply one frame down and that
    -- frame's caller's TCB, both kinds this arm already admits…
    (by intro pp hpp
        cases belowHeadReplyId with
        | none => simp at hpp
        | some rid => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases outerCallerTid with
        | none => simp at hpp
        | some ot => simp at hpp; rw [← hpp]; simp; decide)
    -- …and the state-level lock, now fired by a capability install *or* either
    -- donation's `scThreadIndex` write.
    (by intro pp hpp
        by_cases hc : installsCaps || donatedScId.isSome || redonatedScId.isSome
        · rw [if_pos hc] at hpp
          simp at hpp; rw [← hpp]; simp [stateLevelLock]; decide
        · rw [if_neg hc] at hpp; simp at hpp)

/-- WS-SM SM3.B.4 for `.notificationSignal`. -/
theorem lockSet_consistent_notificationSignal (callerTid : ThreadId)
    (cnRoot nId : ObjId) (wTid : Option ThreadId)
    (boundEndpoint : Option ObjId := none) (boundTcb : Option ThreadId := none)
    -- **WS-OD OD3.10**: stated at the splice-neighbour arity too.  A consistency
    -- proof stated at fewer arguments is a different proposition, and the
    -- default would fill the new one in silently -- the shape RR7.18's census
    -- exists to refuse for the *size* bounds, asked here of the kind check.
    (spliceNeighbors : Option ThreadId × Option ThreadId := (none, none)) :
    ∀ p ∈ (lockSet_notificationSignal callerTid cnRoot nId wTid boundEndpoint boundTcb
             spliceNeighbors).pairs,
      p.fst.kind ∈ permittedKinds .notificationSignal :=
  lockSet_consistent_base_plus_five_opts _ _ _ _ _ _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))
    (by intro pp hpp
        cases wTid with
        | none => simp at hpp
        | some wt => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases boundEndpoint with
        | none => simp at hpp
        | some ep => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases boundTcb with
        | none => simp at hpp
        | some bt => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        obtain ⟨pv?, nx?⟩ := spliceNeighbors
        cases pv? with
        | none => simp at hpp
        | some pv => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        obtain ⟨pv?, nx?⟩ := spliceNeighbors
        cases nx? with
        | none => simp at hpp
        | some nx => simp at hpp; rw [← hpp]; simp; decide)

/-- WS-SM SM3.B.4 for `.declassifySignal` (SM9.C.8).

The notification-signal proof with a fourth optional extension — the
state-level write — because `lockSet_declassifySignal` **is** the signal's set
plus that member.  Deliberately re-derived rather than transported from
`lockSet_consistent_notificationSignal`: the permitted-kinds lists differ (this
one additionally carries `.objStore`), so a transport would need a
monotonicity step whose hypothesis is exactly what a drifted list would
falsify silently. -/
theorem lockSet_consistent_declassifySignal (callerTid : ThreadId)
    (cnRoot nId : ObjId) (wTid : Option ThreadId)
    (boundEndpoint : Option ObjId := none) (boundTcb : Option ThreadId := none) :
    ∀ p ∈ (lockSet_declassifySignal callerTid cnRoot nId wTid boundEndpoint boundTcb).pairs,
      p.fst.kind ∈ permittedKinds .declassifySignal :=
  -- SM9.D.17: a **fifth** optional — the signaller's TCB write upgrade — so the
  -- tier moves with it.  A four-optional builder would still elaborate against
  -- the inner four and leave the outermost member unchecked, which is the
  -- silent-drift shape these builders exist to prevent.
  lockSet_consistent_base_plus_five_opts _ _ _ _ _ _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))
    (by intro pp hpp
        cases wTid with
        | none => simp at hpp
        | some wt => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases boundEndpoint with
        | none => simp at hpp
        | some ep => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases boundTcb with
        | none => simp at hpp
        | some bt => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        simp at hpp; rw [← hpp]; simp; decide)

/-- WS-SM SM3.B.4 for `.notificationWait`. -/
theorem lockSet_consistent_notificationWait (callerTid : ThreadId)
    (cnRoot nId : ObjId) :
    ∀ p ∈ (lockSet_notificationWait callerTid cnRoot nId).pairs,
      p.fst.kind ∈ permittedKinds .notificationWait :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.cspaceMint`. -/
theorem lockSet_consistent_cspaceMint (callerTid : ThreadId)
    (srcCn dstCn : ObjId) :
    ∀ p ∈ (lockSet_cspaceMint callerTid srcCn dstCn).pairs,
      p.fst.kind ∈ permittedKinds .cspaceMint :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        -- WS-RR RR7.9: the state-level member.
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp [stateLevelLock]; decide
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.cspaceCopy`. -/
theorem lockSet_consistent_cspaceCopy (callerTid : ThreadId)
    (srcCn dstCn : ObjId) :
    ∀ p ∈ (lockSet_cspaceCopy callerTid srcCn dstCn).pairs,
      p.fst.kind ∈ permittedKinds .cspaceCopy :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        -- WS-RR RR7.9: the state-level member.
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp [stateLevelLock]; decide
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM6.D / PR #822 Phase H: the `mintReplyCap` lock-set's kinds
(`.tcb`, `.cnode`) are permitted for `.mintReplyCap` (`[.tcb, .cnode]`).  Shares the
`cspaceCopy` footprint, so the proof is identical modulo the syscall tag. -/
theorem lockSet_consistent_mintReplyCap (callerTid : ThreadId)
    (srcCn dstCn : ObjId) :
    ∀ p ∈ (lockSet_mintReplyCap callerTid srcCn dstCn).pairs,
      p.fst.kind ∈ permittedKinds .mintReplyCap :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        -- WS-RR RR7.9: the state-level member.
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp [stateLevelLock]; decide
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.cspaceMove`. -/
theorem lockSet_consistent_cspaceMove (callerTid : ThreadId)
    (srcCn dstCn : ObjId) :
    ∀ p ∈ (lockSet_cspaceMove callerTid srcCn dstCn).pairs,
      p.fst.kind ∈ permittedKinds .cspaceMove :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        -- WS-RR RR7.9: the state-level member.
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp [stateLevelLock]; decide
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.cspaceDelete`. -/
theorem lockSet_consistent_cspaceDelete (callerTid : ThreadId)
    (cnRoot targetCn : ObjId) :
    ∀ p ∈ (lockSet_cspaceDelete callerTid cnRoot targetCn).pairs,
      p.fst.kind ∈ permittedKinds .cspaceDelete :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        -- WS-RR RR7.9: the state-level member.
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp [stateLevelLock]; decide
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.lifecycleRetype`.

PR #873 round 7: stated over **every** `targetLock`, not only the default `none`
— the same widening `lockSet_consistent_declassify` took one round earlier, and
for the same reason: the resolved footprint a fine-lock consumer acquires carries
the re-purposed target, whose kind the state decides. -/
theorem lockSet_consistent_lifecycleRetype (callerTid : ThreadId)
    (cnRoot untypedId dstCn : ObjId) (targetLock : Option LockId := none) :
    ∀ p ∈ (lockSet_lifecycleRetype callerTid cnRoot untypedId dstCn targetLock).pairs,
      p.fst.kind ∈ permittedKinds .lifecycleRetype :=
  lockSet_consistent_base_plus_opt _ _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))
    (by intro pp _
        exact permittedKinds_lifecycleRetype_admits_every_kind pp.fst.kind)

/-- WS-SM SM3.B.4 (PR #873 round 7): **and the members the retype itself takes
are still exactly five.**

The tightness that admitting every target kind would otherwise give up, stated at
`none` — the shape with no resolved target — so drift in the *fixed* part (caller
TCB, caller CSpace root, untyped source, destination CNode, and the state-level
lock) is still a failure even though the theorem above would keep holding of it.

**WS-RR RR7.23 widened the fixed part by one kind, not by convenience.**
`lifecyclePreRetypeCleanup` writes two `SystemState`-level maps — the service
registry when the retyped object is an endpoint
(`cleanupEndpointServiceRegistrations`), and the CDT slot mapping when it is a
CNode — and neither is a per-object field any kind but `.objStore` can name.
Before this member the retype's footprint was provably disjoint from a
concurrent `serviceRegister`'s while both read-modify-wrote `serviceRegistry`. -/
theorem lockSet_lifecycleRetype_nonTarget_kinds (callerTid : ThreadId)
    (cnRoot untypedId dstCn : ObjId) :
    ∀ p ∈ (lockSet_lifecycleRetype callerTid cnRoot untypedId dstCn none).pairs,
      p.fst.kind ∈ [LockKind.tcb, LockKind.cnode, LockKind.untyped, LockKind.objStore] :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp [tcbLock]
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp [cnodeLock]
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp [untypedLock]
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp [cnodeLock]
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp [stateLevelLock]
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.vspaceMap`. -/
theorem lockSet_consistent_vspaceMap (callerTid : ThreadId)
    (cnRoot vId : ObjId) :
    ∀ p ∈ (lockSet_vspaceMap callerTid cnRoot vId).pairs,
      p.fst.kind ∈ permittedKinds .vspaceMap :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM7.D for `.vspaceUnifyInstruction`. -/
theorem lockSet_consistent_vspaceUnifyInstruction (callerTid : ThreadId)
    (cnRoot vId : ObjId) :
    ∀ p ∈ (lockSet_vspaceUnifyInstruction callerTid cnRoot vId).pairs,
      p.fst.kind ∈ permittedKinds .vspaceUnifyInstruction :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.vspaceUnmap`. -/
theorem lockSet_consistent_vspaceUnmap (callerTid : ThreadId)
    (cnRoot vId : ObjId) :
    ∀ p ∈ (lockSet_vspaceUnmap callerTid cnRoot vId).pairs,
      p.fst.kind ∈ permittedKinds .vspaceUnmap :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.serviceRegister`.

Audit-pass-6: the endpoint read lock is now part of the base list.
The literal-list discharge gains one extra `rcases` step. -/
theorem lockSet_consistent_serviceRegister (callerTid : ThreadId)
    (cnRoot epId : ObjId) :
    ∀ p ∈ (lockSet_serviceRegister callerTid cnRoot epId).pairs,
      p.fst.kind ∈ permittedKinds .serviceRegister :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.serviceRevoke`. -/
theorem lockSet_consistent_serviceRevoke (callerTid : ThreadId)
    (cnRoot : ObjId) :
    ∀ p ∈ (lockSet_serviceRevoke callerTid cnRoot).pairs,
      p.fst.kind ∈ permittedKinds .serviceRevoke :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.serviceQuery`. -/
theorem lockSet_consistent_serviceQuery (callerTid : ThreadId)
    (cnRoot : ObjId) :
    ∀ p ∈ (lockSet_serviceQuery callerTid cnRoot).pairs,
      p.fst.kind ∈ permittedKinds .serviceQuery :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.declassify` (SM8.C.9). -/
theorem lockSet_consistent_declassify (callerTid : ThreadId)
    (cnRoot : ObjId) (targetLock : Option LockId := none) :
    ∀ p ∈ (lockSet_declassify callerTid cnRoot targetLock).pairs,
      p.fst.kind ∈ permittedKinds .declassify :=
  -- PR #873 round 6: stated over **every** `targetLock`, not only the default
  -- `none`.  It used to take no such argument, so it proved consistency for the
  -- capless shape alone while the resolved footprint — the one a fine-lock
  -- consumer acquires — could carry a target of any object kind.  A
  -- `permittedKinds` documented as covering "all argument values, including all
  -- possible `Option` cases" was therefore checked against one of them.
  lockSet_consistent_base_plus_opt _ _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))
    (by intro pp _
        exact permittedKinds_declassify_admits_every_kind pp.fst.kind)

/-- WS-SM SM3.B.4 (PR #873 round 6): **and the members the transition itself
takes are still exactly three.**

The tightness that admitting every target kind would otherwise give up.  Stated
at `none` — the shape with no target — so it pins the *fixed* part of the
footprint: the caller's TCB, the caller's CSpace root, and the state-level lock
the trail append needs.  A fourth member appearing here is a failure even though
`lockSet_consistent_declassify` above would still hold of it. -/
theorem lockSet_declassify_nonTarget_kinds (callerTid : ThreadId) (cnRoot : ObjId) :
    ∀ p ∈ (lockSet_declassify callerTid cnRoot none).pairs,
      p.fst.kind ∈ [LockKind.tcb, LockKind.cnode, LockKind.objStore] :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp [tcbLock]
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp [cnodeLock]
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; decide
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.auditRead` (SM9.A.12). -/
theorem lockSet_consistent_auditRead (callerTid : ThreadId)
    (cnRoot : ObjId) :
    ∀ p ∈ (lockSet_auditRead callerTid cnRoot).pairs,
      p.fst.kind ∈ permittedKinds .auditRead :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.auditDrain` (SM9.A.12). -/
theorem lockSet_consistent_auditDrain (callerTid : ThreadId)
    (cnRoot : ObjId) :
    ∀ p ∈ (lockSet_auditDrain callerTid cnRoot).pairs,
      p.fst.kind ∈ permittedKinds .auditDrain :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))

/-- **WS-RR RR7.38**: the queue-owner member's kind obligation, discharged once
for all eleven footprints that carry it.  `QueueOwner.lock_kind` is what makes
this a two-case decision rather than an appeal to a permitted list admitting
everything. -/
theorem queueOwnerMember_kind (q : Option QueueOwner) (permitted : List LockKind)
    (hEp : LockKind.endpoint ∈ permitted)
    (hNtfn : LockKind.notification ∈ permitted) :
    ∀ pp, queueOwnerMember q = some pp → pp.fst.kind ∈ permitted := by
  intro pp hEq
  cases q with
  | none => simp [queueOwnerMember] at hEq
  | some o =>
      simp only [queueOwnerMember, Option.map_some] at hEq
      cases hEq
      rcases o.lock_kind with h | h
      · simpa [h] using hEp
      · simpa [h] using hNtfn

/-- WS-SM SM3.B.4 for `.schedContextConfigure`. -/
theorem lockSet_consistent_schedContextConfigure (callerTid : ThreadId)
    (cnRoot : ObjId) (scid : SchedContextId) (boundTcb : Option ThreadId)
    (queueOwner : Option QueueOwner) :
    ∀ p ∈ (lockSet_schedContextConfigure callerTid cnRoot scid boundTcb queueOwner).pairs,
      p.fst.kind ∈ permittedKinds .schedContextConfigure :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_base_plus_opt _ _ _
      (by intro p hMem
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          exact absurd hMem (by intro h; cases h))
      (by intro pp hpp
          cases boundTcb with
          | none => simp at hpp
          | some bt => simp at hpp; rw [← hpp]; simp; decide))
    (queueOwnerMember_kind queueOwner _ (by decide) (by decide))

/-- WS-SM SM3.B.4 for `.schedContextBind`. -/
theorem lockSet_consistent_schedContextBind (callerTid : ThreadId)
    (cnRoot : ObjId) (scid : SchedContextId) (targetTcb : ThreadId)
    (queueOwner : Option QueueOwner) :
    ∀ p ∈ (lockSet_schedContextBind callerTid cnRoot scid targetTcb queueOwner).pairs,
      p.fst.kind ∈ permittedKinds .schedContextBind :=
  -- WS-OD OD3.5: five base members now — the state-level lock the
  -- `scThreadIndex` maintenance takes joined the four object members.
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_of_extended_base _ _
      (by intro p hMem
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp [stateLevelLock]; decide
          exact absurd hMem (by intro h; cases h)))
    (queueOwnerMember_kind queueOwner _ (by decide) (by decide))

/-- WS-SM SM3.B.4 for `.schedContextUnbind`. -/
theorem lockSet_consistent_schedContextUnbind (callerTid : ThreadId)
    (cnRoot : ObjId) (scid : SchedContextId) (targetTcb : ThreadId)
    (queueOwner : Option QueueOwner) :
    ∀ p ∈ (lockSet_schedContextUnbind callerTid cnRoot scid targetTcb queueOwner).pairs,
      p.fst.kind ∈ permittedKinds .schedContextUnbind :=
  -- WS-OD OD3.5: five base members now — the state-level lock the
  -- `scThreadIndex` maintenance takes joined the four object members.
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_of_extended_base _ _
      (by intro p hMem
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp [stateLevelLock]; decide
          exact absurd hMem (by intro h; cases h)))
    (queueOwnerMember_kind queueOwner _ (by decide) (by decide))

/-- WS-SM SM6.B.4 for `.tcbBindNotification`. -/
theorem lockSet_consistent_tcbBindNotification (callerTid : ThreadId)
    (cnRoot : ObjId) (nId : ObjId) (targetTcb : ThreadId)
    (queueOwner : Option QueueOwner) :
    ∀ p ∈ (lockSet_tcbBindNotification callerTid cnRoot nId targetTcb queueOwner).pairs,
      p.fst.kind ∈ permittedKinds .tcbBindNotification :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_of_extended_base _ _
      (by intro p hMem
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          exact absurd hMem (by intro h; cases h)))
    (queueOwnerMember_kind queueOwner _ (by decide) (by decide))

/-- WS-SM SM6.B.4 for `.tcbUnbindNotification`. -/
theorem lockSet_consistent_tcbUnbindNotification (callerTid : ThreadId)
    (cnRoot : ObjId) (nId : ObjId) (targetTcb : ThreadId)
    (queueOwner : Option QueueOwner) :
    ∀ p ∈ (lockSet_tcbUnbindNotification callerTid cnRoot nId targetTcb queueOwner).pairs,
      p.fst.kind ∈ permittedKinds .tcbUnbindNotification :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_of_extended_base _ _
      (by intro p hMem
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          exact absurd hMem (by intro h; cases h)))
    (queueOwnerMember_kind queueOwner _ (by decide) (by decide))

/-- WS-SM SM3.B.4 for `.tcbSuspend` (audit-pass-3: donation-cancel
extension — 4 optional args; WS-SM SM6.E: + the `consumedReplyId`
reply-link teardown write lock — 5 optional args). -/
theorem lockSet_consistent_tcbSuspend (callerTid : ThreadId)
    (cnRoot : ObjId) (targetTcb : ThreadId)
    (blEp : Option ObjId) (blN : Option ObjId)
    (bindingScId : Option SchedContextId)
    (donatedOriginalOwnerTid : Option ThreadId)
    (consumedReplyId : Option ReplyId := none) :
    ∀ p ∈ (lockSet_tcbSuspend callerTid cnRoot targetTcb blEp blN
              bindingScId donatedOriginalOwnerTid consumedReplyId).pairs,
      p.fst.kind ∈ permittedKinds .tcbSuspend :=
  lockSet_consistent_base_plus_six_opts _ _ _ _ _ _ _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))
    (by intro pp hpp
        cases blEp with
        | none => simp at hpp
        | some ep => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases blN with
        | none => simp at hpp
        | some n => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases bindingScId with
        | none => simp at hpp
        | some sc => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases donatedOriginalOwnerTid with
        | none => simp at hpp
        | some ot => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases consumedReplyId with
        | none => simp at hpp
        | some r => simp at hpp; rw [← hpp]; simp; decide)
    -- WS-OD OD3.5: the donation cancellation's `scThreadIndex` write.
    (by intro pp hpp
        cases bindingScId with
        | none => simp at hpp
        | some _ => simp at hpp; rw [← hpp]; simp [stateLevelLock]; decide)

/-- WS-SM SM3.B.4 for `.tcbResume`. -/
theorem lockSet_consistent_tcbResume (callerTid : ThreadId)
    (cnRoot : ObjId) (targetTcb : ThreadId)
    (queueOwner : Option QueueOwner) :
    ∀ p ∈ (lockSet_tcbResume callerTid cnRoot targetTcb queueOwner).pairs,
      p.fst.kind ∈ permittedKinds .tcbResume :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_of_extended_base _ _
      (by intro p hMem
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          exact absurd hMem (by intro h; cases h)))
    (queueOwnerMember_kind queueOwner _ (by decide) (by decide))

/-- WS-SM SM3.B.4 for `.tcbSetPriority`.

Audit-pass-6: the bound-SC write lock is now an `lockSetExtendOpt`
extension on top of the base list.  Uses `base_plus_opt`. -/
theorem lockSet_consistent_tcbSetPriority (callerTid : ThreadId)
    (cnRoot : ObjId) (targetTcb : ThreadId) (boundSc : Option SchedContextId)
    (queueOwner : Option QueueOwner) :
    ∀ p ∈ (lockSet_tcbSetPriority callerTid cnRoot targetTcb boundSc queueOwner).pairs,
      p.fst.kind ∈ permittedKinds .tcbSetPriority :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_base_plus_opt _ _ _
      (by intro p hMem
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          exact absurd hMem (by intro h; cases h))
      (by intro pp hpp
          cases boundSc with
          | none => simp at hpp
          | some sc => simp at hpp; rw [← hpp]; simp; decide))
    (queueOwnerMember_kind queueOwner _ (by decide) (by decide))

/-- WS-SM SM3.B.4 for `.tcbSetMCPriority`.

Audit-pass-6: same shape as `.tcbSetPriority`. -/
theorem lockSet_consistent_tcbSetMCPriority (callerTid : ThreadId)
    (cnRoot : ObjId) (targetTcb : ThreadId) (boundSc : Option SchedContextId)
    (queueOwner : Option QueueOwner) :
    ∀ p ∈ (lockSet_tcbSetMCPriority callerTid cnRoot targetTcb boundSc queueOwner).pairs,
      p.fst.kind ∈ permittedKinds .tcbSetMCPriority :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_base_plus_opt _ _ _
      (by intro p hMem
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          exact absurd hMem (by intro h; cases h))
      (by intro pp hpp
          cases boundSc with
          | none => simp at hpp
          | some sc => simp at hpp; rw [← hpp]; simp; decide))
    (queueOwnerMember_kind queueOwner _ (by decide) (by decide))

/-- WS-SM SM3.B.4 for `.tcbSetIPCBuffer`.

Audit-pass-6: the target-VSpaceRoot read lock is now an
`lockSetExtendOpt` extension on top of the base list.  Uses
`base_plus_opt`. -/
theorem lockSet_consistent_tcbSetIPCBuffer (callerTid : ThreadId)
    (cnRoot : ObjId) (targetTcb : ThreadId) (targetVSpaceRoot : Option ObjId)
    (queueOwner : Option QueueOwner) :
    ∀ p ∈ (lockSet_tcbSetIPCBuffer callerTid cnRoot targetTcb targetVSpaceRoot queueOwner).pairs,
      p.fst.kind ∈ permittedKinds .tcbSetIPCBuffer :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_base_plus_opt _ _ _
      (by intro p hMem
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          exact absurd hMem (by intro h; cases h))
      (by intro pp hpp
          cases targetVSpaceRoot with
          | none => simp at hpp
          | some vsr => simp at hpp; rw [← hpp]; simp; decide))
    (queueOwnerMember_kind queueOwner _ (by decide) (by decide))

/-- WS-SM SM5.H.4 for `.tcbSetAffinity`.

Same shape as `.tcbSetPriority`: the base three locks (caller TCB read, CNode read,
target TCB write) plus the optional bound-SchedContext write. -/
theorem lockSet_consistent_tcbSetAffinity (callerTid : ThreadId)
    (cnRoot : ObjId) (targetTcb : ThreadId) (boundSc : Option SchedContextId)
    (queueOwner : Option QueueOwner) :
    ∀ p ∈ (lockSet_tcbSetAffinity callerTid cnRoot targetTcb boundSc queueOwner).pairs,
      p.fst.kind ∈ permittedKinds .tcbSetAffinity :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_base_plus_opt _ _ _
      (by intro p hMem
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          rcases List.mem_cons.mp hMem with h | hMem
          · rw [h]; simp; decide
          exact absurd hMem (by intro h; cases h))
      (by intro pp hpp
          cases boundSc with
          | none => simp at hpp
          | some sc => simp at hpp; rw [← hpp]; simp; decide))
    (queueOwnerMember_kind queueOwner _ (by decide) (by decide))

/-- PR #887 review, for `.tcbSetFaultHandler`: the base three locks plus the
optional target-CNode read and (review round 3) the optional read of the
endpoint the CPtr names. -/
theorem lockSet_consistent_tcbSetFaultHandler (callerTid : ThreadId)
    (cnRoot : ObjId) (targetTcb : ThreadId) (targetCnRoot : Option ObjId)
    (handlerEp : Option ObjId)
    (queueOwner : Option QueueOwner) :
    ∀ p ∈ (lockSet_tcbSetFaultHandler callerTid cnRoot targetTcb targetCnRoot handlerEp queueOwner).pairs,
      p.fst.kind ∈ permittedKinds .tcbSetFaultHandler :=
  lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_extendOpt _ _ _
      (lockSet_consistent_base_plus_opt _ _ _
        (by intro p hMem
            rcases List.mem_cons.mp hMem with h | hMem
            · rw [h]; simp; decide
            rcases List.mem_cons.mp hMem with h | hMem
            · rw [h]; simp; decide
            rcases List.mem_cons.mp hMem with h | hMem
            · rw [h]; simp; decide
            exact absurd hMem (by intro h; cases h))
        (by intro pp hpp
            cases targetCnRoot with
            | none => simp at hpp
            | some cn => simp at hpp; rw [← hpp]; simp; decide))
      (by intro pp hpp
          cases handlerEp with
          | none => simp at hpp
          | some ep => simp at hpp; rw [← hpp]; simp; decide))
    (queueOwnerMember_kind queueOwner _ (by decide) (by decide))

end SeLe4n.Kernel.Concurrency
