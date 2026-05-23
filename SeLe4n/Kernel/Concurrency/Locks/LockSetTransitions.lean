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

## Audit-pass-2 scope clarification: donation and PIP-chain locks

For the 6 syscalls that may traverse a SchedContext-donation path
(`endpointCall`, `endpointReply`, `replyRecv`, `tcbSuspend`,
`schedContextBind`, `schedContextUnbind`) or trigger
priority-inheritance-propagation (any IPC syscall on a blocking
chain), the **statically-declared lockSet covers only the
directly-named objects** in the syscall args.

The donation path can additionally touch:

* the donated `SchedContext` (write — `boundThread` field is
  rebound),
* the original-owner `TCB` (write — schedContextBinding field
  transitions out of `.donated` / back to `.bound`).

These are state-discovered (located via the replier's TCB's
`schedContextBinding` field) rather than statically named in the
syscall args.  Per plan §4.1's "pre-resolved Option arg" pattern,
a future audit pass could add `donatedScId : Option SchedContextId`
and `originalOwnerTid : Option ThreadId` parameters to the
affected `lockSet_<τ>` functions, with the caller pre-inspecting
the replier's TCB (under a temporary read-lock) before computing
the full lockSet.

The plan §5.2's example `lockSet_endpointCall` does NOT model the
donation path either, so this implementation matches the plan's
level of detail.  SM3.C's `withLockSet` combinator can handle
donation-chain locks via a documented sub-call pattern
(acquire-inspect-extend-acquire-rest) without breaking 2PL —
the inspection happens between the initial lock-set acquisition
and the action body.

PIP-chain TCB locks (one per blocking ancestor) are inherently
dynamic and cannot be modelled in a static lockSet.  Plan §4.1's
"deadlock-freedom requires knowing the lock-set in advance"
discipline applies via the SM0.I lock-id total order: PIP-chain
TCBs are at hierarchy level `.tcb` and are acquired in `ObjId.val`
ascending order, preserving the lock-ladder invariant.

The `permittedKinds` declarations in this module reflect the
static lockSet's footprint; dynamic donation/PIP-chain locks
extend the actually-held set at acquisition time but never the
declared lockSet.
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

/-- WS-SM SM3.B: build the LockId for a SchedContext at the given
SchedContextId. -/
@[inline] def schedContextLock (scid : SchedContextId) : LockId :=
  ⟨.schedContext, scid.toObjId⟩

/-- WS-SM SM3.B: build the LockId for a VSpaceRoot at the given ObjId. -/
@[inline] def vspaceRootLock (oid : ObjId) : LockId :=
  ⟨.vspaceRoot, oid⟩

/-- WS-SM SM3.B: build the LockId for an Untyped object at the given
ObjId. -/
@[inline] def untypedLock (oid : ObjId) : LockId :=
  ⟨.untyped, oid⟩

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
*union over all paths*. -/
def lockSet_endpointSend (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (endpointObjId : ObjId)
    (receiverTid : Option ThreadId) : LockSet :=
  lockSetExtendOpt
    (lockSetOfList
      [(tcbLock callerTid, .write),
       (cnodeLock cnodeRootObjId, .read),
       (endpointLock endpointObjId, .write)])
    (receiverTid.map (fun rt => (tcbLock rt, .write)))

/-- WS-SM SM3.B.3: `lockSet` for `endpointReceive` (syscall `.receive`).

Symmetric to `send`: caller TCB blocks/unblocks; endpoint queue
mutates; optional sender TCB completes its handshake. -/
def lockSet_endpointReceive (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (endpointObjId : ObjId)
    (senderTid : Option ThreadId) : LockSet :=
  lockSetExtendOpt
    (lockSetOfList
      [(tcbLock callerTid, .write),
       (cnodeLock cnodeRootObjId, .read),
       (endpointLock endpointObjId, .write)])
    (senderTid.map (fun st => (tcbLock st, .write)))

/-- WS-SM SM3.B.3: `lockSet` for `endpointCall` (syscall `.call`).

A blocking RPC: caller TCB writes, endpoint writes, optional
receiver TCB writes (same shape as send + receive combined). -/
def lockSet_endpointCall (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (endpointObjId : ObjId)
    (receiverTid : Option ThreadId) : LockSet :=
  lockSetExtendOpt
    (lockSetOfList
      [(tcbLock callerTid, .write),
       (cnodeLock cnodeRootObjId, .read),
       (endpointLock endpointObjId, .write)])
    (receiverTid.map (fun rt => (tcbLock rt, .write)))

/-- WS-SM SM3.B.3: `lockSet` for `endpointReply` (syscall `.reply`).

Caller TCB (write — clearing blocked state); reply target TCB
(write — transitioning out of `BlockedReply`). -/
def lockSet_endpointReply (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (replyTargetTid : ThreadId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .write),
     (cnodeLock cnodeRootObjId, .read),
     (tcbLock replyTargetTid, .write)]

/-- WS-SM SM3.B.3: `lockSet` for `replyRecv` (syscall `.replyRecv`).

Combined reply + receive in one transition.  Touches the caller
TCB (write — both reply-clearing and receive-blocking phases), the
endpoint (write — queue mutation in the receive phase), the
prior-call reply target TCB (write — completes the reply), and an
optional new sender TCB (write — if a sender was already
waiting). -/
def lockSet_replyRecv (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (replyTargetTid : ThreadId)
    (endpointObjId : ObjId) (newSenderTid : Option ThreadId) : LockSet :=
  lockSetExtendOpt
    (lockSetOfList
      [(tcbLock callerTid, .write),
       (cnodeLock cnodeRootObjId, .read),
       (tcbLock replyTargetTid, .write),
       (endpointLock endpointObjId, .write)])
    (newSenderTid.map (fun st => (tcbLock st, .write)))

/-! ## Notification syscalls (2 transitions) -/

/-- WS-SM SM3.B.3: `lockSet` for `notificationSignal`.

The signaller's TCB does NOT mutate (signal is non-blocking from
caller's perspective) — but we conservatively include it in read
mode since the signal path inspects the caller's identity for
badge attribution.  The notification mutates (waiter dequeue or
badge merge); the optional waiter TCB mutates (wake-up). -/
def lockSet_notificationSignal (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (notificationObjId : ObjId)
    (waiterTid : Option ThreadId) : LockSet :=
  lockSetExtendOpt
    (lockSetOfList
      [(tcbLock callerTid, .read),
       (cnodeLock cnodeRootObjId, .read),
       (notificationLock notificationObjId, .write)])
    (waiterTid.map (fun wt => (tcbLock wt, .write)))

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
CNode (write — minted cap is stored). -/
def lockSet_cspaceMint (callerTid : ThreadId)
    (srcCnodeObjId dstCnodeObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock srcCnodeObjId, .read),
     (cnodeLock dstCnodeObjId, .write)]

/-- WS-SM SM3.B.3: `lockSet` for `cspaceCopy`.  Same shape as `mint`. -/
def lockSet_cspaceCopy (callerTid : ThreadId)
    (srcCnodeObjId dstCnodeObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock srcCnodeObjId, .read),
     (cnodeLock dstCnodeObjId, .write)]

/-- WS-SM SM3.B.3: `lockSet` for `cspaceMove`.

Both source and destination CNodes are mutated (cap removed from
src, inserted to dst). -/
def lockSet_cspaceMove (callerTid : ThreadId)
    (srcCnodeObjId dstCnodeObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock srcCnodeObjId, .write),
     (cnodeLock dstCnodeObjId, .write)]

/-- WS-SM SM3.B.3: `lockSet` for `cspaceDelete`.

The target CNode is the only structural mutation; the caller's
CSpace root is read for the cap-lookup path. -/
def lockSet_cspaceDelete (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (targetCnodeObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read),
     (cnodeLock targetCnodeObjId, .write)]

/-! ## Lifecycle syscalls (1 transition: lifecycleRetype) -/

/-- WS-SM SM3.B.3: `lockSet` for `lifecycleRetype`.

Caller TCB (read), untyped source (write — watermark advance,
child list append), destination CNode (write — caps installed for
the new objects). -/
def lockSet_lifecycleRetype (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (untypedObjId : ObjId)
    (dstCnodeObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read),
     (untypedLock untypedObjId, .write),
     (cnodeLock dstCnodeObjId, .write)]

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

/-! ## Service syscalls (3 transitions)

Services are tracked at the SystemState level (not as per-object
RHTable entries); they take the ObjStore-level lock implicitly via
their registry table reads/writes.  At SM3.B per-object level, the
caller TCB and the relevant CNode are the only per-object locks. -/

/-- WS-SM SM3.B.3: `lockSet` for `serviceRegister`. -/
def lockSet_serviceRegister (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read)]

/-- WS-SM SM3.B.3: `lockSet` for `serviceRevoke`. -/
def lockSet_serviceRevoke (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read)]

/-- WS-SM SM3.B.3: `lockSet` for `serviceQuery`. -/
def lockSet_serviceQuery (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read)]

/-! ## SchedContext syscalls (3 transitions) -/

/-- WS-SM SM3.B.3: `lockSet` for `schedContextConfigure`.

The SchedContext mutates (budget/period/priority/deadline fields);
its bound TCB (if any) may need its `domain` field rewritten to
match the new SC domain (per the R5.G domain-propagation block). -/
def lockSet_schedContextConfigure (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (scid : SchedContextId)
    (boundTcbTid : Option ThreadId) : LockSet :=
  lockSetExtendOpt
    (lockSetOfList
      [(tcbLock callerTid, .read),
       (cnodeLock cnodeRootObjId, .read),
       (schedContextLock scid, .write)])
    (boundTcbTid.map (fun bt => (tcbLock bt, .write)))

/-- WS-SM SM3.B.3: `lockSet` for `schedContextBind`. -/
def lockSet_schedContextBind (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (scid : SchedContextId)
    (targetTcbTid : ThreadId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read),
     (schedContextLock scid, .write),
     (tcbLock targetTcbTid, .write)]

/-- WS-SM SM3.B.3: `lockSet` for `schedContextUnbind`. -/
def lockSet_schedContextUnbind (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (scid : SchedContextId)
    (targetTcbTid : ThreadId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read),
     (schedContextLock scid, .write),
     (tcbLock targetTcbTid, .write)]

/-! ## TCB lifecycle and config syscalls (5 transitions) -/

/-- WS-SM SM3.B.3: `lockSet` for `tcbSuspend`.

Target TCB (write — state transition to `.Inactive`); optional
endpoint/notification if the target is blocked on one (write —
queue removal). -/
def lockSet_tcbSuspend (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (targetTcbTid : ThreadId)
    (blockedEndpointObjId : Option ObjId)
    (blockedNotificationObjId : Option ObjId) : LockSet :=
  let base := lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read),
     (tcbLock targetTcbTid, .write)]
  let withEp := lockSetExtendOpt base
    (blockedEndpointObjId.map (fun ep => (endpointLock ep, .write)))
  lockSetExtendOpt withEp
    (blockedNotificationObjId.map (fun n => (notificationLock n, .write)))

/-- WS-SM SM3.B.3: `lockSet` for `tcbResume`.

Target TCB (write — state transition to `.Ready`).  The scheduler
state (run queue) mutates implicitly through the TCB's `objects`
write at SM3.B; SM4 will lift the scheduler to per-core state. -/
def lockSet_tcbResume (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (targetTcbTid : ThreadId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read),
     (tcbLock targetTcbTid, .write)]

/-- WS-SM SM3.B.3: `lockSet` for `tcbSetPriority`. -/
def lockSet_tcbSetPriority (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (targetTcbTid : ThreadId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read),
     (tcbLock targetTcbTid, .write)]

/-- WS-SM SM3.B.3: `lockSet` for `tcbSetMCPriority`. -/
def lockSet_tcbSetMCPriority (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (targetTcbTid : ThreadId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read),
     (tcbLock targetTcbTid, .write)]

/-- WS-SM SM3.B.3: `lockSet` for `tcbSetIPCBuffer`. -/
def lockSet_tcbSetIPCBuffer (callerTid : ThreadId)
    (cnodeRootObjId : ObjId) (targetTcbTid : ThreadId) : LockSet :=
  lockSetOfList
    [(tcbLock callerTid, .read),
     (cnodeLock cnodeRootObjId, .read),
     (tcbLock targetTcbTid, .write)]

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
  -- IPC syscalls
  | .send | .receive | .call =>
      [.tcb, .cnode, .endpoint]
  | .reply =>
      [.tcb, .cnode]
  | .replyRecv =>
      [.tcb, .cnode, .endpoint]
  -- Notification syscalls
  | .notificationSignal | .notificationWait =>
      [.tcb, .cnode, .notification]
  -- Capability syscalls
  | .cspaceMint | .cspaceCopy | .cspaceMove | .cspaceDelete =>
      [.tcb, .cnode]
  -- Lifecycle
  | .lifecycleRetype =>
      [.tcb, .cnode, .untyped]
  -- VSpace syscalls
  | .vspaceMap | .vspaceUnmap =>
      [.tcb, .cnode, .vspaceRoot]
  -- Service syscalls
  | .serviceRegister | .serviceRevoke | .serviceQuery =>
      [.tcb, .cnode]
  -- SchedContext syscalls
  | .schedContextConfigure | .schedContextBind | .schedContextUnbind =>
      [.tcb, .cnode, .schedContext]
  -- TCB lifecycle/config
  | .tcbSuspend =>
      [.tcb, .cnode, .endpoint, .notification]
  | .tcbResume | .tcbSetPriority | .tcbSetMCPriority | .tcbSetIPCBuffer =>
      [.tcb, .cnode]

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
has kind in `permittedKinds .send`. -/
theorem lockSet_consistent_send (callerTid : ThreadId)
    (cnRoot epId : ObjId) (rTid : Option ThreadId) :
    ∀ p ∈ (lockSet_endpointSend callerTid cnRoot epId rTid).pairs,
      p.fst.kind ∈ permittedKinds .send :=
  lockSet_consistent_base_plus_opt _ _ _
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

/-- WS-SM SM3.B.4 for `.receive`. -/
theorem lockSet_consistent_receive (callerTid : ThreadId)
    (cnRoot epId : ObjId) (sTid : Option ThreadId) :
    ∀ p ∈ (lockSet_endpointReceive callerTid cnRoot epId sTid).pairs,
      p.fst.kind ∈ permittedKinds .receive :=
  lockSet_consistent_base_plus_opt _ _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))
    (by intro pp hpp
        cases sTid with
        | none => simp at hpp
        | some st => simp at hpp; rw [← hpp]; simp; decide)

/-- WS-SM SM3.B.4 for `.call`. -/
theorem lockSet_consistent_call (callerTid : ThreadId)
    (cnRoot epId : ObjId) (rTid : Option ThreadId) :
    ∀ p ∈ (lockSet_endpointCall callerTid cnRoot epId rTid).pairs,
      p.fst.kind ∈ permittedKinds .call :=
  lockSet_consistent_base_plus_opt _ _ _
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

/-- WS-SM SM3.B.4 for `.reply`. -/
theorem lockSet_consistent_reply (callerTid : ThreadId)
    (cnRoot : ObjId) (rTid : ThreadId) :
    ∀ p ∈ (lockSet_endpointReply callerTid cnRoot rTid).pairs,
      p.fst.kind ∈ permittedKinds .reply :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.replyRecv`. -/
theorem lockSet_consistent_replyRecv (callerTid : ThreadId)
    (cnRoot : ObjId) (rTid : ThreadId) (epId : ObjId)
    (newSenderTid : Option ThreadId) :
    ∀ p ∈ (lockSet_replyRecv callerTid cnRoot rTid epId newSenderTid).pairs,
      p.fst.kind ∈ permittedKinds .replyRecv :=
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
        exact absurd hMem (by intro h; cases h))
    (by intro pp hpp
        cases newSenderTid with
        | none => simp at hpp
        | some st => simp at hpp; rw [← hpp]; simp; decide)

/-- WS-SM SM3.B.4 for `.notificationSignal`. -/
theorem lockSet_consistent_notificationSignal (callerTid : ThreadId)
    (cnRoot nId : ObjId) (wTid : Option ThreadId) :
    ∀ p ∈ (lockSet_notificationSignal callerTid cnRoot nId wTid).pairs,
      p.fst.kind ∈ permittedKinds .notificationSignal :=
  lockSet_consistent_base_plus_opt _ _ _
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
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.lifecycleRetype`. -/
theorem lockSet_consistent_lifecycleRetype (callerTid : ThreadId)
    (cnRoot untypedId dstCn : ObjId) :
    ∀ p ∈ (lockSet_lifecycleRetype callerTid cnRoot untypedId dstCn).pairs,
      p.fst.kind ∈ permittedKinds .lifecycleRetype :=
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

/-- WS-SM SM3.B.4 for `.serviceRegister`. -/
theorem lockSet_consistent_serviceRegister (callerTid : ThreadId)
    (cnRoot : ObjId) :
    ∀ p ∈ (lockSet_serviceRegister callerTid cnRoot).pairs,
      p.fst.kind ∈ permittedKinds .serviceRegister :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
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
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.schedContextConfigure`. -/
theorem lockSet_consistent_schedContextConfigure (callerTid : ThreadId)
    (cnRoot : ObjId) (scid : SchedContextId) (boundTcb : Option ThreadId) :
    ∀ p ∈ (lockSet_schedContextConfigure callerTid cnRoot scid boundTcb).pairs,
      p.fst.kind ∈ permittedKinds .schedContextConfigure :=
  lockSet_consistent_base_plus_opt _ _ _
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
        | some bt => simp at hpp; rw [← hpp]; simp; decide)

/-- WS-SM SM3.B.4 for `.schedContextBind`. -/
theorem lockSet_consistent_schedContextBind (callerTid : ThreadId)
    (cnRoot : ObjId) (scid : SchedContextId) (targetTcb : ThreadId) :
    ∀ p ∈ (lockSet_schedContextBind callerTid cnRoot scid targetTcb).pairs,
      p.fst.kind ∈ permittedKinds .schedContextBind :=
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

/-- WS-SM SM3.B.4 for `.schedContextUnbind`. -/
theorem lockSet_consistent_schedContextUnbind (callerTid : ThreadId)
    (cnRoot : ObjId) (scid : SchedContextId) (targetTcb : ThreadId) :
    ∀ p ∈ (lockSet_schedContextUnbind callerTid cnRoot scid targetTcb).pairs,
      p.fst.kind ∈ permittedKinds .schedContextUnbind :=
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

/-- WS-SM SM3.B.4 for `.tcbSuspend`. -/
theorem lockSet_consistent_tcbSuspend (callerTid : ThreadId)
    (cnRoot : ObjId) (targetTcb : ThreadId)
    (blEp : Option ObjId) (blN : Option ObjId) :
    ∀ p ∈ (lockSet_tcbSuspend callerTid cnRoot targetTcb blEp blN).pairs,
      p.fst.kind ∈ permittedKinds .tcbSuspend :=
  lockSet_consistent_base_plus_two_opts _ _ _ _
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

/-- WS-SM SM3.B.4 for `.tcbResume`. -/
theorem lockSet_consistent_tcbResume (callerTid : ThreadId)
    (cnRoot : ObjId) (targetTcb : ThreadId) :
    ∀ p ∈ (lockSet_tcbResume callerTid cnRoot targetTcb).pairs,
      p.fst.kind ∈ permittedKinds .tcbResume :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.tcbSetPriority`. -/
theorem lockSet_consistent_tcbSetPriority (callerTid : ThreadId)
    (cnRoot : ObjId) (targetTcb : ThreadId) :
    ∀ p ∈ (lockSet_tcbSetPriority callerTid cnRoot targetTcb).pairs,
      p.fst.kind ∈ permittedKinds .tcbSetPriority :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.tcbSetMCPriority`. -/
theorem lockSet_consistent_tcbSetMCPriority (callerTid : ThreadId)
    (cnRoot : ObjId) (targetTcb : ThreadId) :
    ∀ p ∈ (lockSet_tcbSetMCPriority callerTid cnRoot targetTcb).pairs,
      p.fst.kind ∈ permittedKinds .tcbSetMCPriority :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))

/-- WS-SM SM3.B.4 for `.tcbSetIPCBuffer`. -/
theorem lockSet_consistent_tcbSetIPCBuffer (callerTid : ThreadId)
    (cnRoot : ObjId) (targetTcb : ThreadId) :
    ∀ p ∈ (lockSet_tcbSetIPCBuffer callerTid cnRoot targetTcb).pairs,
      p.fst.kind ∈ permittedKinds .tcbSetIPCBuffer :=
  lockSet_consistent_of_extended_base _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))

end SeLe4n.Kernel.Concurrency
