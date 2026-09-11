-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.LockSet

/-!
# WS-SM SM3.B — LockSet regression suite (plan §5.2.SM3.B.9)

Tier-2 / Tier-3 surface anchors + decidable examples + runtime
structural assertions for every public symbol introduced by SM3.B
(LockSet / LockIdProjection / LockSetTransitions / LockSetInventory).

The suite exercises four families of checks:

* **Surface anchors** (§1).  Every public SM3.B symbol is
  `#check`'d so a rename or signature drift fails the suite at
  elaboration time.

* **Decidable defaults** (§2).  `LockSet.empty`, `singleton`,
  `insert?`, `insertOrMerge`, `union`, `containsKey`, and the
  per-transition `lockSet_<τ>` declarations are checked at
  elaboration time via `decide`.

* **Sort / ordering / completeness** (§3).  Decidable examples on
  small concrete `LockSet`s exercise `lockAcquireSequence`'s
  ordered / complete / canonical properties.

* **Runtime assertions** (§4).  Per-transition consistency and
  inventory aggregator checks run at `lake exe lock_set_suite`
  and assert via `assertBool`.
-/

namespace SeLe4n.Testing.LockSet

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1 — Surface anchors
-- ============================================================================

/-! ## SM3.B.1 — KernelObject.lockKind + LockId.fromObject -/

#check @KernelObject.lockKind
#check @KernelObject.lockKind_tcb
#check @KernelObject.lockKind_endpoint
#check @KernelObject.lockKind_notification
#check @KernelObject.lockKind_cnode
#check @KernelObject.lockKind_vspaceRoot
#check @KernelObject.lockKind_untyped
#check @KernelObject.lockKind_schedContext
#check @KernelObject.lockKind_exists
#check @KernelObject.lockKind_eq_of_objectType
#check @KernelObject.lockKind_in_modeledKinds
#check @KernelObject.lockKind_ne_objStore
#check @KernelObject.lockKind_reply
#check @KernelObject.lockKind_ne_page
#check @LockId.fromObject
#check @LockId.fromObject_kind
#check @LockId.fromObject_objId

/-! ## SM3.B.2 — LockId.lookup -/

#check @LockId.lookup
#check @LockId.lookup_some_of_kindMatch
#check @LockId.lookup_fromObject_of_present
#check @LockId.lookup_objStore
#check @LockId.lookup_reply
#check @LockId.lookup_page
#check @LockId.lookup_kindMatch
#check @LockId.lookup_lockState_eq

/-! ## SM3.B.5..B.8 — LockSet structure + canonical sort + theorems -/

#check @LockSet
#check @LockSet.empty
#check @LockSet.singleton
#check @LockSet.insert?
#check @LockSet.insertOrMerge
#check @LockSet.union
#check @LockSet.containsKey
#check @LockSet.size
#check @LockSet.lockAcquireSequence
#check @LockSet.lockAcquireSequence_ordered
#check @LockSet.lockAcquireSequence_complete
#check @LockSet.lockAcquireSequence_canonical
#check @LockSet.lockAcquireSequence_length
#check @LockSet.lockAcquireSequence_perm
#check @LockSet.fst_inj_at_pairs

/-! ## SM3.B AccessMode algebra -/

#check @AccessMode.lub
#check @AccessMode.lub_idem
#check @AccessMode.lub_comm
#check @AccessMode.lub_assoc
#check @AccessMode.conflicts
#check @AccessMode.conflicts_symm

/-! ## SM3.B LockSet structural helpers -/

#check @LockSet.insertOrMerge_mem
#check @LockSet.union_mem_inv
#check @LockSet.empty_pairs
#check @LockSet.singleton_pairs
#check @LockSet.union_empty
#check @LockSet.containsKey_iff

/-! ## SM3.B.3 — Per-transition lockSet declarations -/

#check @lockSet_endpointSend
#check @lockSet_endpointReceive
#check @lockSet_endpointCall
#check @lockSet_endpointReply
#check @lockSet_replyRecv
#check @lockSet_notificationSignal
#check @lockSet_notificationWait
#check @lockSet_cspaceMint
#check @lockSet_cspaceCopy
#check @lockSet_cspaceMove
#check @lockSet_cspaceDelete
#check @lockSet_lifecycleRetype
#check @lockSet_vspaceMap
#check @lockSet_vspaceUnmap
#check @lockSet_serviceRegister
#check @lockSet_serviceRevoke
#check @lockSet_serviceQuery
#check @lockSet_schedContextConfigure
#check @lockSet_schedContextBind
#check @lockSet_schedContextUnbind
#check @SeLe4n.Kernel.lockSet_tcbSuspendOnCore
#check @lockSet_tcbResume
#check @lockSet_tcbSetPriority
#check @lockSet_tcbSetMCPriority
#check @lockSet_tcbSetIPCBuffer
#check @lockSet_tcbSetAffinity
#check @lockSet_tcbSetFaultHandler

/-! ## SM3.B.3 audit-pass-5 — PIP-chain-walk start markers -/

#check @pipChainStart_endpointCall
#check @pipChainStart_endpointReply
#check @pipChainStart_replyRecv
#check @pipChainStart_replyRecvReceiveLeg
#check @pipChainStart_endpointReceive

/-! ## SM3.B.4 — Per-transition consistency theorems -/

#check @permittedKinds
#check @lockSet_consistent_send
#check @lockSet_consistent_receive
#check @lockSet_consistent_call
#check @lockSet_consistent_reply
#check @lockSet_consistent_replyRecv
#check @lockSet_consistent_notificationSignal
#check @lockSet_consistent_notificationWait
#check @lockSet_consistent_cspaceMint
#check @lockSet_consistent_cspaceCopy
#check @lockSet_consistent_cspaceMove
#check @lockSet_consistent_cspaceDelete
#check @lockSet_consistent_lifecycleRetype
#check @lockSet_consistent_vspaceMap
#check @lockSet_consistent_vspaceUnmap
#check @lockSet_consistent_serviceRegister
#check @lockSet_consistent_serviceRevoke
#check @lockSet_consistent_serviceQuery
#check @lockSet_consistent_schedContextConfigure
#check @lockSet_consistent_schedContextBind
#check @lockSet_consistent_schedContextUnbind
#check @SeLe4n.Kernel.lockSet_tcbSuspendOnCore_correct
#check @lockSet_consistent_tcbResume
#check @lockSet_consistent_tcbSetPriority
#check @lockSet_consistent_tcbSetMCPriority
#check @lockSet_consistent_tcbSetIPCBuffer
#check @lockSet_consistent_tcbSetAffinity
#check @lockSet_consistent_tcbSetFaultHandler

/-! ## SM3.B Inventory -/

#check @LockSetCategory
#check @LockSetTheorem
#check @lockSetTheorems
#check @lockSetTheorems_count
#check @lockSetTheorems_projection_count
#check @lockSetTheorems_lockSet_count
#check @lockSetTheorems_consistency_count
#check @lockSetTheorems_acquireSort_count
#check @lockSetTheorems_algebra_count
#check @lockSetTheorems_chainStart_count
#check @lockSetTheorems_partition_sum
#check @lockSetTheorems_identifiers_nodup
#check @lockSetTheorems_descriptions_nodup
#check @lockSet_consistent_aggregate_covers_every_syscall

-- ============================================================================
-- §2 — Decidable defaults (empty, singleton, simple constructions)
-- ============================================================================

/-! ### Empty lock-set -/

example : LockSet.empty.pairs = [] := by decide
example : LockSet.empty.size = 0 := by decide
example : LockSet.empty.containsKey ⟨.tcb, ObjId.ofNat 1⟩ = false := by decide
-- lockAcquireSequence uses List.mergeSort whose internal `O(n log n)` recursion
-- is opaque to `decide`'s kernel reduction.  `native_decide` compiles to
-- native code and discharges the equality in microseconds with the same
-- kernel-checked trust base.
example : (LockSet.empty.lockAcquireSequence = []) := by native_decide

/-! ### Singleton lock-set -/

example : (LockSet.singleton ⟨.tcb, ObjId.ofNat 1⟩ .write).pairs =
    [(⟨.tcb, ObjId.ofNat 1⟩, .write)] := by decide

example : (LockSet.singleton ⟨.endpoint, ObjId.ofNat 5⟩ .read).size = 1 := by decide

example : (LockSet.singleton ⟨.cnode, ObjId.ofNat 7⟩ .read).containsKey
    ⟨.cnode, ObjId.ofNat 7⟩ = true := by decide

/-! ### Insert?  -/

example : (LockSet.empty.insert? ⟨.tcb, ObjId.ofNat 1⟩ .write).isSome := by decide

example :
    let S := LockSet.singleton ⟨.tcb, ObjId.ofNat 1⟩ .write
    (S.insert? ⟨.tcb, ObjId.ofNat 1⟩ .read) = none := by decide

example :
    let S := LockSet.singleton ⟨.tcb, ObjId.ofNat 1⟩ .write
    (S.insert? ⟨.endpoint, ObjId.ofNat 5⟩ .write).isSome := by decide

/-! ### InsertOrMerge merges via lub (write dominates read) -/

example :
    let S := LockSet.singleton ⟨.tcb, ObjId.ofNat 1⟩ .read
    (S.insertOrMerge ⟨.tcb, ObjId.ofNat 1⟩ .write).pairs =
      [(⟨.tcb, ObjId.ofNat 1⟩, .write)] := by decide

example :
    let S := LockSet.singleton ⟨.tcb, ObjId.ofNat 1⟩ .write
    (S.insertOrMerge ⟨.tcb, ObjId.ofNat 1⟩ .read).pairs =
      [(⟨.tcb, ObjId.ofNat 1⟩, .write)] := by decide

/-! ### AccessMode algebra (decidable) -/

example : AccessMode.lub .read .write = .write := by decide
example : AccessMode.lub .write .read = .write := by decide
example : AccessMode.lub .read .read = .read := by decide
example : AccessMode.lub .write .write = .write := by decide

example : AccessMode.conflicts .read .read = false := by decide
example : AccessMode.conflicts .write .read = true := by decide
example : AccessMode.conflicts .read .write = true := by decide
example : AccessMode.conflicts .write .write = true := by decide

-- ============================================================================
-- §3 — Sort / ordering / completeness (decidable on small concrete sets)
-- ============================================================================

/-! ### lockAcquireSequence on a 3-element set sorts by LockId ascending.

The set contains (tcb 5 write), (cnode 10 read), (endpoint 20 write).
The kind levels are: cnode=2, tcb=3, endpoint=4.  Expected sort:
cnode/10 (read), tcb/5 (write), endpoint/20 (write). -/

private def threeLockSet : LockSet :=
  LockSet.empty.insertOrMerge ⟨.endpoint, ObjId.ofNat 20⟩ .write
    |>.insertOrMerge ⟨.tcb, ObjId.ofNat 5⟩ .write
    |>.insertOrMerge ⟨.cnode, ObjId.ofNat 10⟩ .read

example : threeLockSet.size = 3 := by decide

example : threeLockSet.lockAcquireSequence =
    [(⟨.cnode, ObjId.ofNat 10⟩, .read),
     (⟨.tcb, ObjId.ofNat 5⟩, .write),
     (⟨.endpoint, ObjId.ofNat 20⟩, .write)] := by native_decide

/-! ### Same kind, different ObjIds: sort by ObjId.val ascending.

Set: (tcb 7 write), (tcb 3 write), (tcb 5 write).
Expected sort: tcb/3, tcb/5, tcb/7. -/

private def threeTcbLockSet : LockSet :=
  LockSet.empty.insertOrMerge ⟨.tcb, ObjId.ofNat 7⟩ .write
    |>.insertOrMerge ⟨.tcb, ObjId.ofNat 3⟩ .write
    |>.insertOrMerge ⟨.tcb, ObjId.ofNat 5⟩ .write

example : threeTcbLockSet.lockAcquireSequence =
    [(⟨.tcb, ObjId.ofNat 3⟩, .write),
     (⟨.tcb, ObjId.ofNat 5⟩, .write),
     (⟨.tcb, ObjId.ofNat 7⟩, .write)] := by native_decide

/-! ### Lub-merging when the same key appears twice in input.

Audit-pass-1 addition: `insertOrMerge` must collapse duplicate keys
via `AccessMode.lub`.  This is a real correctness scenario for
`lockSet_tcbSuspendOnCore` when `callerTid = targetTcbTid` (self-suspend).

Order should not matter — read+write = write regardless of which
is inserted first. -/

example :
    let S := LockSet.empty.insertOrMerge ⟨.tcb, ObjId.ofNat 5⟩ .read
              |>.insertOrMerge ⟨.tcb, ObjId.ofNat 5⟩ .write
    S.size = 1 ∧ S.pairs = [(⟨.tcb, ObjId.ofNat 5⟩, .write)] := by decide

example :
    let S := LockSet.empty.insertOrMerge ⟨.tcb, ObjId.ofNat 5⟩ .write
              |>.insertOrMerge ⟨.tcb, ObjId.ofNat 5⟩ .read
    S.size = 1 ∧ S.pairs = [(⟨.tcb, ObjId.ofNat 5⟩, .write)] := by decide

-- read + read = read (no upgrade)
example :
    let S := LockSet.empty.insertOrMerge ⟨.tcb, ObjId.ofNat 5⟩ .read
              |>.insertOrMerge ⟨.tcb, ObjId.ofNat 5⟩ .read
    S.pairs = [(⟨.tcb, ObjId.ofNat 5⟩, .read)] := by decide

/-! ### Self-suspend (`callerTid = targetTcbTid`) collapses TCB locks.

The cancellation root contributes (tcb target, write) and the suspend footprint
adds (tcb caller, read) and (cnode root, read).  With caller=target, the lub-merge
produces (tcb caller, write), so the total is 2.

**WS-OD (`v0.35.4`)**: taken over `lockSet_tcbSuspendOnCore` at the *default*
state, where the target resolves to no TCB — the arm that declares the victim's
lock and nothing else, which is exactly the shape this merge is about.  The
parametric `lockSet_tcbSuspend` this used to read is retired; its members are
now resolved from the state the pipeline runs on. -/

example :
    let S := SeLe4n.Kernel.lockSet_tcbSuspendOnCore default ⟨5⟩ (ObjId.ofNat 10) ⟨5⟩
    S.size = 2 := by native_decide

example :
    let S := SeLe4n.Kernel.lockSet_tcbSuspendOnCore default ⟨5⟩ (ObjId.ofNat 10) ⟨5⟩
    S.lockAcquireSequence =
      [(⟨.cnode, ObjId.ofNat 10⟩, .read),
       (⟨.tcb, ObjId.ofNat 5⟩, .write)] := by native_decide

/-! ### Reply with caller = reply-target collapses to two locks.

`lockSet_endpointReply` declares (caller TCB, write), (cnode, read),
(reply target, write).  If caller = reply target, the merge yields
a single (TCB, write) entry. -/

example :
    let S := lockSet_endpointReply ⟨5⟩ (ObjId.ofNat 10) ⟨5⟩ none none none none none
    S.size = 2 := by decide

-- ============================================================================
-- §4 — Per-transition lockSet shape examples
-- ============================================================================

/-! ### endpointSend with no receiver: 3 locks. -/

example :
    (lockSet_endpointSend ⟨1⟩ (ObjId.ofNat 10) (ObjId.ofNat 20) none).size = 3 :=
  by decide

/-! ### endpointSend with a receiver: 4 locks. -/

example :
    (lockSet_endpointSend ⟨1⟩ (ObjId.ofNat 10) (ObjId.ofNat 20) (some ⟨2⟩)).size = 4 :=
  by decide

/-! ### endpointCall lock-set sort matches plan §4.5 example.

Plan §4.5: endpointCall with caller TCB 5, CNode 10, endpoint 20,
receiver TCB 8.  Sort: cnode/10, tcb/5, tcb/8, endpoint/20.

Audit-pass-3: the donation arg is `none` for this example (caller
has no active SC to donate). -/

example :
    LockSet.lockAcquireSequence
      (lockSet_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
        (some ⟨8⟩) none) =
    [(⟨.cnode, ObjId.ofNat 10⟩, .read),
     (⟨.tcb, ObjId.ofNat 5⟩, .write),
     (⟨.tcb, ObjId.ofNat 8⟩, .write),
     (⟨.endpoint, ObjId.ofNat 20⟩, .write)] := by native_decide

/-! ### endpointCall with donation: caller TCB 5 has SC 100,
calling receiver TCB 8 (passive).  SC is donated, so SC lock
included. -/

example :
    LockSet.lockAcquireSequence
      (lockSet_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
        (some ⟨8⟩) (some ⟨100⟩)) =
    -- WS-OD OD3.5: a donating call also holds the state-level lock, for the
    -- `scThreadIndex` maintenance `donateSchedContext` ends in.  It is level 0,
    -- so the ladder puts it first.
    [(⟨.objStore, ObjId.ofNat 0⟩, .write),
     (⟨.cnode, ObjId.ofNat 10⟩, .read),
     (⟨.tcb, ObjId.ofNat 5⟩, .write),
     (⟨.tcb, ObjId.ofNat 8⟩, .write),
     (⟨.endpoint, ObjId.ofNat 20⟩, .write),
     (⟨.schedContext, ObjId.ofNat 100⟩, .write)] := by native_decide

/-! ### The suspend's optional members, at the two footprints that own them.

**WS-OD (`v0.35.4`)**: the parametric `lockSet_tcbSuspend` carried the victim's
blocked object, its consumed Reply and its SchedContext binding as its own
arguments; it is retired, and those members now belong to the two footprints the
pipeline's sub-operations declare — the teardown's
(`lockSet_cancelIpcBlocking`, which the suspend footprint is *built over*) and
the donation cancellation's (`lockSet_cancelDonation`).  The sizes below are the
same members counted where they now live: the suspend footprint adds the
caller's TCB read and the CSpace root read on top of the teardown's. -/

/-! ### Teardown with both a blocked endpoint and a blocked notification: 3. -/

example :
    (SeLe4n.Kernel.lockSet_cancelIpcBlocking ⟨3⟩
      (some (ObjId.ofNat 20)) (some (ObjId.ofNat 30)) none none none none
      (none, none) none none none none).size = 3 := by decide

/-! ### Teardown with no blocked objects: the victim's TCB alone. -/

example :
    (SeLe4n.Kernel.lockSet_cancelIpcBlocking ⟨3⟩ none none none none none none
      (none, none) none none none none).size = 1 := by decide

/-! ### Donation cancellation of a `.donated` binding: 4 (victim + donated SC +
original owner + — WS-OD OD3.5 — the state-level lock the `scThreadIndex` write
takes).  The pop's three stack members are `none` on a context heading no
stack. -/

example :
    (SeLe4n.Kernel.lockSet_cancelDonation ⟨3⟩ (some ⟨50⟩) (some ⟨7⟩)
      none none none).size = 4 := by decide

/-! ### …of a `.bound` binding: 3 (victim + bound SC + the state-level lock). -/

example :
    (SeLe4n.Kernel.lockSet_cancelDonation ⟨3⟩ (some ⟨50⟩) none
      none none none).size = 3 := by decide

/-! ### WS-SM SM6.E — teardown of a `.blockedOnReply` target: 2 (the victim and
the Reply object its reply link is consumed from). -/

example :
    (SeLe4n.Kernel.lockSet_cancelIpcBlocking ⟨3⟩ none none (some ⟨60⟩) none none none
      (none, none) none none none none).size = 2 := by decide

/-! ### WS-OD (`v0.35.4`) — …and the pop's own three stack objects, on the
donated arm that performs it: 7. -/

example :
    (SeLe4n.Kernel.lockSet_cancelDonation ⟨3⟩ (some ⟨50⟩) (some ⟨7⟩)
      (some ⟨60⟩) (some ⟨61⟩) (some ⟨9⟩)).size = 7 := by decide

-- ============================================================================
-- §5 — LockId.fromObject + LockId.lookup with fixture states
-- ============================================================================

/-! ### LockId.fromObject reflects KernelObject.lockKind -/

example :
    let oid := ObjId.ofNat 5
    let ep : Endpoint := {}
    let l := LockId.fromObject oid (KernelObject.endpoint ep)
    l = ⟨.endpoint, oid⟩ := rfl

example :
    let oid := ObjId.ofNat 7
    let u : UntypedObject :=
      { regionBase := PAddr.ofNat 0, regionSize := 4096 }
    let l := LockId.fromObject oid (KernelObject.untyped u)
    l = ⟨.untyped, oid⟩ := rfl

/-! ### LockId.lookup on the empty SystemState returns none -/

example :
    LockId.lookup (default : SystemState) ⟨.tcb, ObjId.ofNat 1⟩ = none := by decide

example :
    LockId.lookup (default : SystemState) ⟨.endpoint, ObjId.ofNat 99⟩ = none := by
  decide

/-! ### LockId.lookup on the empty SystemState for `.objStore`/`.reply`/`.page`
returns none — fail-closed for N/A kinds. -/

example :
    LockId.lookup (default : SystemState) ⟨.objStore, ObjId.ofNat 0⟩ = none := by
  decide

example :
    LockId.lookup (default : SystemState) ⟨.reply, ObjId.ofNat 0⟩ = none := by
  decide

example :
    LockId.lookup (default : SystemState) ⟨.page, ObjId.ofNat 0⟩ = none := by
  decide

/-! ### LockId.lookup on a state with an inserted Endpoint.

Audit-pass-1 addition: tests the `some` branch of `LockId.lookup`.
After inserting an Endpoint at ObjId 5, lookup at `(.endpoint, 5)`
returns `some (lock, object)` and lookup at any other kind+ObjId
returns `none` (the kind-confusion fail-closed branch). -/

private def stateWithEndpoint : SystemState :=
  let s : SystemState := default
  let ep : KernelObject := KernelObject.endpoint ({} : Endpoint)
  { s with objects := s.objects.insert (ObjId.ofNat 5) ep }

example :
    (LockId.lookup stateWithEndpoint ⟨.endpoint, ObjId.ofNat 5⟩).isSome :=
  by native_decide

/-! ### Kind mismatch fail-closed: a TCB-tagged LockId at an
ObjId storing an Endpoint resolves to `none`. -/

example :
    LockId.lookup stateWithEndpoint ⟨.tcb, ObjId.ofNat 5⟩ = none := by
  native_decide

example :
    LockId.lookup stateWithEndpoint ⟨.cnode, ObjId.ofNat 5⟩ = none := by
  native_decide

/-! ### Lookup at an unrelated ObjId is none. -/

example :
    LockId.lookup stateWithEndpoint ⟨.endpoint, ObjId.ofNat 99⟩ = none := by
  native_decide

-- ============================================================================
-- §6 — Permitted kinds for every syscall
-- ============================================================================

-- WS-RR RR7.7: `.objStore` — a capability-carrying rendezvous writes the CDT
-- maps, whose declared subject is `stateLevelLock` (kind `.objStore`).
example : permittedKinds .send = [.tcb, .cnode, .endpoint, .objStore] := by decide
-- WS-SM SM6.D: `.receive` gains `.reply` — a `Call` rendezvous on the receive
-- path links a server-supplied Reply object (`linkCallerReply` writes `reply.caller`
-- under the per-object reply write-lock).
-- WS-RR RR7.11: `.objStore` — the receive leg installs through the same
-- `ipcTransferSingleCap` the send does, and writes the same CDT maps.
-- WS-OD OD3.6: `.schedContext` — a receive that dequeues a queued `Call`
-- donates that caller's scheduling context to the receiver (seL4-MCS's
-- `receiveIPC`), reaching the same donation primitive `.call` does.
example : permittedKinds .receive
    = [.tcb, .cnode, .endpoint, .schedContext, .reply, .objStore] := by decide
-- Audit-pass-3: `.call`/`.reply`/`.replyRecv` include `.schedContext` for the
-- donation extension.  WS-SM SM6.D: they also gain `.reply` — each links or
-- consumes a first-class Reply object under the per-object reply write-lock.
example : permittedKinds .call = [.tcb, .cnode, .endpoint, .schedContext, .reply, .objStore] := by decide
-- WS-OD OD3.5: `.objStore` joins `.reply` — the donation return maintains
-- `scThreadIndex`, an `RHTable` whose insert may rehash the whole table.
example : permittedKinds .reply =
    [.tcb, .cnode, .schedContext, .reply, .objStore] := by decide
example : permittedKinds .replyRecv =
    [.tcb, .cnode, .endpoint, .schedContext, .reply, .objStore] := by decide
-- WS-SM SM6.B: `.notificationSignal` gains `.endpoint` for the bound-delivery
-- dequeue (a signal to a notification whose bound TCB is BlockedOnReceive removes
-- it from its endpoint); `.notificationWait` is unchanged.
example : permittedKinds .notificationSignal = [.tcb, .cnode, .notification, .endpoint] := by decide
example : permittedKinds .notificationWait = [.tcb, .cnode, .notification] := by decide
-- WS-RR RR7.9: `.objStore` joins all four — every capability operation writes
-- the CDT (three mint nodes and add an edge, the delete removes one), and
-- `stateLevelLock` is that structure's declared subject.
example : permittedKinds .cspaceMint = [.tcb, .cnode, .objStore] := by decide
example : permittedKinds .cspaceCopy = [.tcb, .cnode, .objStore] := by decide
example : permittedKinds .cspaceMove = [.tcb, .cnode, .objStore] := by decide
example : permittedKinds .cspaceDelete = [.tcb, .cnode, .objStore] := by decide
-- PR #873 round 7: `.lifecycleRetype` admits EVERY kind too, and for the same
-- reason `.declassify` does below.  SM9.D.12 makes the retype the arm that
-- *clears* taint at `args.targetObj`, so `lockSet_lifecycleRetype` carries that
-- target's own lock — and a retype re-purposes an object whose kind the state,
-- not the syscall, decides.  The fixed four stay pinned by
-- `lockSet_lifecycleRetype_nonTarget_kinds`.
example : permittedKinds .lifecycleRetype =
    [.tcb, .cnode, .untyped,
     .objStore, .endpoint, .notification, .reply, .schedContext, .vspaceRoot, .page] := by decide
example : permittedKinds .vspaceMap = [.tcb, .cnode, .vspaceRoot] := by decide
example : permittedKinds .vspaceUnmap = [.tcb, .cnode, .vspaceRoot] := by decide
-- WS-RR RR7.23: `.objStore` on all three — `serviceRegistry` is a
-- `SystemState`-level map and `stateLevelLock` is the only member that can name
-- it; before this the trio carried the coverage as a convention.
example : permittedKinds .serviceRegister = [.tcb, .cnode, .endpoint, .objStore] := by decide
example : permittedKinds .serviceRevoke = [.tcb, .cnode, .objStore] := by decide
example : permittedKinds .serviceQuery = [.tcb, .cnode, .objStore] := by decide
-- WS-RR RR7.38: `.endpoint` and `.notification` join every arm that can write a
-- *queued* TCB — the queue owner's lock, whose kind `QueueOwner.lock_kind` fixes
-- to exactly these two.  The lists are pinned whole, so a third kind is still a
-- failure here.
example : permittedKinds .schedContextConfigure =
    [.tcb, .cnode, .schedContext, .endpoint, .notification] := by decide
-- WS-OD OD3.5: the bind and the unbind gain `.objStore` for their
-- `scThreadIndex` maintenance; `.schedContextConfigure` writes no index and is
-- deliberately not widened with them.
example : permittedKinds .schedContextBind =
    [.tcb, .cnode, .schedContext, .endpoint, .notification, .objStore] := by decide
example : permittedKinds .schedContextUnbind =
    [.tcb, .cnode, .schedContext, .endpoint, .notification, .objStore] := by decide
-- Audit-pass-3: `.tcbSuspend` now includes `.schedContext` to cover
-- the donation-cancel extension.  WS-SM SM6.E: + `.reply` to cover the
-- `.blockedOnReply` reply-link teardown (`consumeReplyLink`).
-- WS-OD OD3.5: + `.objStore`, for the donation cancellation's `scThreadIndex`
-- maintenance — the same reason `.reply` gained it.
example : permittedKinds .tcbSuspend =
    [.tcb, .cnode, .endpoint, .notification, .schedContext, .reply, .objStore] := by decide
example : permittedKinds .tcbResume = [.tcb, .cnode, .endpoint, .notification] := by decide
example : permittedKinds .tcbSetPriority =
    [.tcb, .cnode, .schedContext, .endpoint, .notification] := by decide
example : permittedKinds .tcbSetMCPriority =
    [.tcb, .cnode, .schedContext, .endpoint, .notification] := by decide
example : permittedKinds .tcbSetIPCBuffer =
    [.tcb, .cnode, .vspaceRoot, .endpoint, .notification] := by decide
-- PR #873 round 6: `.declassify` admits EVERY kind, and that is a statement
-- about the arm rather than a relaxation.  The live arm hands
-- `cap.target = .object targetId` to a transition that commits a `storeObject`
-- at it, and SM9.D.17's `targetLock : Option LockId` carries that object's own
-- lock into the resolved footprint — so a downgrade of an endpoint, a
-- notification, a reply, a scheduling context, a VSpace root, an untyped region
-- or a page frame contributes that kind.  Listing three left
-- `lockSet_consistent_declassify` provable only at the default `none` while the
-- resolved footprint could carry a kind the inventory did not admit.
example : permittedKinds .declassify =
    [.tcb, .cnode, .objStore,
     .untyped, .endpoint, .notification, .reply, .schedContext, .vspaceRoot, .page] := by decide
-- ...and the fixed part stays three.  This is the tightness the widening would
-- otherwise give up: a fourth member on the no-target shape is a failure even
-- though the consistency theorem above would still hold of it.
example : permittedKinds .declassifySignal =
    [.tcb, .cnode, .notification, .endpoint, .objStore] := by decide
example : permittedKinds .auditRead = [.tcb, .cnode, .objStore] := by decide
example : permittedKinds .auditDrain = [.tcb, .cnode, .objStore] := by decide

-- ============================================================================
-- §6b — LockSet.union semantics
-- ============================================================================

/-! ### Union with empty is identity.

The `union_empty` `@[simp]` theorem gives this for free, but the
runtime check ensures the `foldl` computation actually behaves
identity on the empty right-argument. -/

example : (LockSet.singleton ⟨.tcb, ObjId.ofNat 1⟩ .write).union LockSet.empty =
    LockSet.singleton ⟨.tcb, ObjId.ofNat 1⟩ .write := by decide

/-! ### Union of disjoint LockSets contains both keys. -/

example :
    let S1 := LockSet.singleton ⟨.tcb, ObjId.ofNat 1⟩ .write
    let S2 := LockSet.singleton ⟨.endpoint, ObjId.ofNat 2⟩ .write
    (S1.union S2).size = 2 := by decide

/-! ### Union merges overlapping keys via lub. -/

example :
    let S1 := LockSet.singleton ⟨.tcb, ObjId.ofNat 1⟩ .read
    let S2 := LockSet.singleton ⟨.tcb, ObjId.ofNat 1⟩ .write
    (S1.union S2).pairs = [(⟨.tcb, ObjId.ofNat 1⟩, .write)] := by decide

-- ============================================================================
-- §6c — Runtime exercise of lockSet_consistent_* on concrete args
-- ============================================================================

/-! ### Every per-transition `lockSet_consistent_*` theorem actually
holds on concrete arguments.  Audit-pass-1 addition: surface-anchors
are only `#check`'d, so a `True`-typed identity would pass.  The
runtime exercise below specialises each theorem to concrete args and
verifies the universally-quantified claim. -/

example :
    ∀ p ∈ (lockSet_endpointSend ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
              (some ⟨8⟩)).pairs,
      p.fst.kind ∈ permittedKinds .send :=
  lockSet_consistent_send ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20) (some ⟨8⟩)

example :
    ∀ p ∈ (lockSet_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
              (some ⟨8⟩) none).pairs,
      p.fst.kind ∈ permittedKinds .call :=
  lockSet_consistent_call ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
    (some ⟨8⟩) none

-- Audit-pass-3: with donation arg, all kinds still in permitted set.
example :
    ∀ p ∈ (lockSet_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
              (some ⟨8⟩) (some ⟨100⟩)).pairs,
      p.fst.kind ∈ permittedKinds .call :=
  lockSet_consistent_call ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
    (some ⟨8⟩) (some ⟨100⟩)

-- WS-RR RR7.7: and with a capability-transfer destination, on both arms.  The
-- consistency theorems are stated over every `destCnode`, so these instantiate
-- the argument the pre-RR7.7 statements defaulted away.
example :
    ∀ p ∈ (lockSet_endpointSend ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
              (some ⟨8⟩) (some (ObjId.ofNat 42))).pairs,
      p.fst.kind ∈ permittedKinds .send :=
  lockSet_consistent_send ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20) (some ⟨8⟩)
    (some (ObjId.ofNat 42))

example :
    ∀ p ∈ (lockSet_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
              (some ⟨8⟩) (some ⟨100⟩) (some ⟨7⟩) (some (ObjId.ofNat 42))).pairs,
      p.fst.kind ∈ permittedKinds .call :=
  lockSet_consistent_call ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
    (some ⟨8⟩) (some ⟨100⟩) (some ⟨7⟩) (some (ObjId.ofNat 42))

-- **WS-OD (`v0.35.4`)**: the `.tcbSuspend` kinds are checked at the two
-- footprints that declare them — the teardown's, at its widest arm, and the
-- donation cancellation's — plus the state-resolved suspend footprint the
-- dispatcher actually hands the bracket.
example :
    ∀ p ∈ (SeLe4n.Kernel.lockSet_cancelIpcBlocking ⟨3⟩
              (some (ObjId.ofNat 20)) (some (ObjId.ofNat 30)) (some ⟨60⟩)
              (some ⟨50⟩) (some ⟨7⟩) (some (ObjId.ofNat 21))
              (some ⟨8⟩, some ⟨9⟩) (some ⟨61⟩) (some ⟨11⟩)
              (some ⟨62⟩) (some ⟨63⟩)).pairs,
      p.fst.kind ∈ permittedKinds .tcbSuspend :=
  SeLe4n.Kernel.lockSet_consistent_cancelIpcBlocking ⟨3⟩
    (some (ObjId.ofNat 20)) (some (ObjId.ofNat 30)) (some ⟨60⟩)
    (some ⟨50⟩) (some ⟨7⟩) (some (ObjId.ofNat 21))
    (some ⟨8⟩, some ⟨9⟩) (some ⟨61⟩) (some ⟨11⟩) (some ⟨62⟩) (some ⟨63⟩)

example :
    ∀ p ∈ (SeLe4n.Kernel.lockSet_cancelDonation ⟨3⟩ (some ⟨50⟩) (some ⟨7⟩)
              (some ⟨60⟩) (some ⟨61⟩) (some ⟨9⟩)).pairs,
      p.fst.kind ∈ permittedKinds .tcbSuspend :=
  SeLe4n.Kernel.lockSet_consistent_cancelDonation ⟨3⟩ (some ⟨50⟩) (some ⟨7⟩)
    (some ⟨60⟩) (some ⟨61⟩) (some ⟨9⟩)

example :
    ∀ p ∈ (SeLe4n.Kernel.lockSet_tcbSuspendOnCore default ⟨5⟩ (ObjId.ofNat 10)
              ⟨3⟩).pairs,
      p.fst.kind ∈ permittedKinds .tcbSuspend :=
  SeLe4n.Kernel.lockSet_tcbSuspendOnCore_correct default ⟨5⟩ (ObjId.ofNat 10) ⟨3⟩

example :
    ∀ p ∈ (lockSet_schedContextBind ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩ ⟨3⟩ none).pairs,
      p.fst.kind ∈ permittedKinds .schedContextBind :=
  lockSet_consistent_schedContextBind ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩ ⟨3⟩ none

example :
    ∀ p ∈ (lockSet_lifecycleRetype ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
              (ObjId.ofNat 30)).pairs,
      p.fst.kind ∈ permittedKinds .lifecycleRetype :=
  lockSet_consistent_lifecycleRetype ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
    (ObjId.ofNat 30)

-- ============================================================================
-- §6d — Runtime exercise of lockAcquireSequence_canonical
-- ============================================================================

/-! ### The canonical-sort theorem actually applies: given an
already-sorted permutation, `lockAcquireSequence` returns the same. -/

example :
    let S := lockSet_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
              (some ⟨8⟩) none
    let canonical : List (LockId × AccessMode) :=
      [(⟨.cnode, ObjId.ofNat 10⟩, .read),
       (⟨.tcb, ObjId.ofNat 5⟩, .write),
       (⟨.tcb, ObjId.ofNat 8⟩, .write),
       (⟨.endpoint, ObjId.ofNat 20⟩, .write)]
    canonical = S.lockAcquireSequence := by native_decide

-- ============================================================================
-- §6e — pipChainStart_* (audit-pass-5) PIP chain-walk start markers
-- ============================================================================

/-! ### pipChainStart_endpointCall mirrors receiverTid exactly.

When there is no waiting receiver (`receiverTid = none`), no PIP
propagation occurs and the chain-start signal is `none`.  When a
receiver is waiting, PIP propagates from the receiver and the
chain-start signal equals `some receiverTid`. -/

example :
    pipChainStart_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20) none none
      = none := by decide

example :
    pipChainStart_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
      (some ⟨8⟩) none = some ⟨8⟩ := by decide

example :
    pipChainStart_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
      (some ⟨8⟩) (some ⟨100⟩) = some ⟨8⟩ := by decide

/-! ### pipChainStart_endpointReply always emits revertPIP at caller. -/

example :
    pipChainStart_endpointReply ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩ none none
      = some ⟨5⟩ := by decide

example :
    pipChainStart_endpointReply ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩
      (some ⟨42⟩) (some ⟨7⟩) = some ⟨5⟩ := by decide

/-! ### pipChainStart_replyRecv emits revertPIP at the **recorded server**.

WS-OD OD3.14: the reply leg's walk starts at the thread whose waiter set it
shrank, which is the recorded server — the receiver itself on a non-delegated
reply, and a different thread when the reply capability was delegated.  Naming
the receiver there would send the SM3.C walker up a different chain. -/

example :
    pipChainStart_replyRecv ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩ (ObjId.ofNat 20)
      none none none ⟨5⟩ = some ⟨5⟩ := by decide

example :
    pipChainStart_replyRecv ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩ (ObjId.ofNat 20)
      (some ⟨11⟩) (some ⟨42⟩) (some ⟨7⟩) ⟨9⟩ = some ⟨9⟩ := by decide

/-! ### pipChainStart_replyRecvReceiveLeg (WS-OD OD3.14) — the SECOND walk.

`none` on a non-delegated reply, because the reply leg's own walk started at the
receiver and **is** this walk; `none` when the receive leg dequeued nothing;
and the receiver otherwise. -/

example :
    pipChainStart_replyRecvReceiveLeg ⟨5⟩ ⟨5⟩ (some ⟨11⟩) = none := by decide

example :
    pipChainStart_replyRecvReceiveLeg ⟨5⟩ ⟨9⟩ none = none := by decide

example :
    pipChainStart_replyRecvReceiveLeg ⟨5⟩ ⟨9⟩ (some ⟨11⟩) = some ⟨5⟩ := by decide

/-! ### pipChainStart_endpointReceive (WS-OD OD3.14) — the walk `.receive`
gained when the priority inversion on its rendezvous path was closed.

Mirrors the dequeued caller exactly: a receive that blocked, and a plain `Send`
rendezvous, invoke no walk. -/

example :
    pipChainStart_endpointReceive ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20) none
      = none := by decide

example :
    pipChainStart_endpointReceive ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20) (some ⟨11⟩)
      = some ⟨5⟩ := by decide

/-! ### pipChainStart_tcbSuspend (SM6.E) walks only when the victim was
reply-blocked — the signal is exactly the G2-precaptured blocking server. -/

example :
    pipChainStart_tcbSuspend ⟨5⟩ none = none := by decide

example :
    pipChainStart_tcbSuspend ⟨5⟩ (some ⟨8⟩) = some ⟨8⟩ := by decide

-- ============================================================================
-- §7 — Inventory examples (decidable)
-- ============================================================================

example : lockSetTheorems.length = 113 := by decide

example : (lockSetTheorems.filter (fun t => t.category == .projection)).length = 22 := by
  decide

example : (lockSetTheorems.filter (fun t => t.category == .lockSet)).length = 35 := by
  decide

example : (lockSetTheorems.filter (fun t => t.category == .consistency)).length = 35 := by
  decide

example : (lockSetTheorems.filter (fun t => t.category == .acquireSort)).length = 6 := by
  decide

example : (lockSetTheorems.filter (fun t => t.category == .algebra)).length = 9 := by
  decide

example : (lockSetTheorems.filter (fun t => t.category == .chainStart)).length = 6 := by
  decide

-- ============================================================================
-- §8 — Runtime assertions
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

private def runLockSetCoreChecks : IO Unit := do
  IO.println "--- §1 Empty / Singleton ---"
  assertBool "LockSet.empty.pairs = []"
    (decide (LockSet.empty.pairs = []))
  assertBool "LockSet.empty.size = 0"
    (decide (LockSet.empty.size = 0))
  let tcb1 : LockId := ⟨.tcb, ObjId.ofNat 1⟩
  assertBool "containsKey on empty returns false"
    (decide (LockSet.empty.containsKey tcb1 = false))
  assertBool "singleton tcb1 write size = 1"
    (decide ((LockSet.singleton tcb1 .write).size = 1))
  assertBool "singleton tcb1 write contains tcb1"
    (decide ((LockSet.singleton tcb1 .write).containsKey tcb1 = true))

private def runLockSetAcquireSortChecks : IO Unit := do
  IO.println "--- §2 Acquire sort ---"
  -- Plan §4.5 example: caller TCB 5, CNode 10, endpoint 20, receiver TCB 8.
  -- Audit-pass-3: donation arg is none (no SC active for this caller).
  let s := lockSet_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20) (some ⟨8⟩) none
  let seq := s.lockAcquireSequence
  assertBool "endpointCall lock-set size = 4 (no donation)"
    (decide (s.size = 4))
  assertBool "endpointCall lockAcquireSequence length = 4 (no donation)"
    (decide (seq.length = 4))
  -- The sort is deterministic: cnode/10 (read), tcb/5 (write), tcb/8 (write), endpoint/20 (write).
  let expected : List (LockId × AccessMode) :=
    [(⟨.cnode, ObjId.ofNat 10⟩, .read),
     (⟨.tcb, ObjId.ofNat 5⟩, .write),
     (⟨.tcb, ObjId.ofNat 8⟩, .write),
     (⟨.endpoint, ObjId.ofNat 20⟩, .write)]
  assertBool "endpointCall lockAcquireSequence matches plan §4.5 expected order"
    (decide (seq = expected))
  -- Audit-pass-3: with donation, the SC is added and sorts last (level 7).
  -- **WS-OD OD3.5**: and the state-level lock joins it, because
  -- `donateSchedContext` maintains `SystemState.scThreadIndex` -- an `RHTable`
  -- whose insert may rehash, so no per-object lock decomposes it.  Six members,
  -- and the `.objStore` singleton sorts FIRST (`LockKind` level 0), which is
  -- what keeps the by-kind ladder acyclic: the state-level lock is taken before
  -- any per-object one.
  let sDon := lockSet_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
                (some ⟨8⟩) (some ⟨100⟩)
  let seqDon := sDon.lockAcquireSequence
  assertBool "endpointCall (with donation) lock-set size = 6"
    (decide (sDon.size = 6))
  let expectedDon : List (LockId × AccessMode) :=
    [(stateLevelLock, .write),
     (⟨.cnode, ObjId.ofNat 10⟩, .read),
     (⟨.tcb, ObjId.ofNat 5⟩, .write),
     (⟨.tcb, ObjId.ofNat 8⟩, .write),
     (⟨.endpoint, ObjId.ofNat 20⟩, .write),
     (⟨.schedContext, ObjId.ofNat 100⟩, .write)]
  assertBool "endpointCall (with donation) lockAcquireSequence: objStore first, SC last"
    (decide (seqDon = expectedDon))

private def runAccessModeAlgebraChecks : IO Unit := do
  IO.println "--- §3 AccessMode algebra ---"
  assertBool "lub .read .write = .write" (decide (AccessMode.lub .read .write = .write))
  assertBool "lub .write .read = .write" (decide (AccessMode.lub .write .read = .write))
  assertBool "lub .read .read = .read" (decide (AccessMode.lub .read .read = .read))
  assertBool "lub .write .write = .write" (decide (AccessMode.lub .write .write = .write))
  assertBool "conflicts .read .read = false" (decide (AccessMode.conflicts .read .read = false))
  assertBool "conflicts .read .write = true" (decide (AccessMode.conflicts .read .write = true))
  assertBool "conflicts .write .read = true" (decide (AccessMode.conflicts .write .read = true))
  assertBool "conflicts .write .write = true" (decide (AccessMode.conflicts .write .write = true))

private def runPermittedKindsChecks : IO Unit := do
  IO.println "--- §4 PermittedKinds ---"
  -- WS-RR RR7.7: `.objStore` joins, for the CDT maps a capability-carrying
  -- rendezvous writes; `stateLevelLock` is that write's declared subject.
  assertBool "permittedKinds .send"
    (decide (permittedKinds .send = [.tcb, .cnode, .endpoint, .objStore]))
  assertBool "permittedKinds .vspaceMap"
    (decide (permittedKinds .vspaceMap = [.tcb, .cnode, .vspaceRoot]))
  -- PR #873 round 7: every kind, because the retype's taint clear keys on
  -- `args.targetObj`, whose type the state decides.  The fixed four are pinned
  -- separately by `lockSet_lifecycleRetype_nonTarget_kinds`.
  assertBool "permittedKinds .lifecycleRetype"
    (decide (permittedKinds .lifecycleRetype =
      [.tcb, .cnode, .untyped,
       .objStore, .endpoint, .notification, .reply, .schedContext, .vspaceRoot, .page]))
  -- WS-RR RR7.23: five members, four kinds — the state-level lock joined the
  -- fixed part because `lifecyclePreRetypeCleanup` sweeps the service registry
  -- (an endpoint being re-purposed) and detaches CDT slot mappings (a CNode),
  -- and neither map is nameable by a per-object kind.
  assertBool "NEGATIVE: the retype's fixed footprint is still exactly four kinds"
    ((lockSet_lifecycleRetype ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
        (ObjId.ofNat 30) none).pairs.all (fun p =>
      decide (p.fst.kind ∈
        [LockKind.tcb, LockKind.cnode, LockKind.untyped, LockKind.objStore])))
  -- WS-RR RR7.23 (register finding 5): every registry writer declares the
  -- state-level lock — the trio in write/write/read, and the retype.
  assertBool "serviceRegister declares the registry's state-level write"
    ((lockSet_serviceRegister ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)).pairs.any (fun p =>
      decide (p.fst = stateLevelLock ∧ p.snd = AccessMode.write)))
  assertBool "serviceRevoke declares the registry's state-level write"
    ((lockSet_serviceRevoke ⟨5⟩ (ObjId.ofNat 10)).pairs.any (fun p =>
      decide (p.fst = stateLevelLock ∧ p.snd = AccessMode.write)))
  assertBool "serviceQuery declares the registry's state-level read"
    ((lockSet_serviceQuery ⟨5⟩ (ObjId.ofNat 10)).pairs.any (fun p =>
      decide (p.fst = stateLevelLock ∧ p.snd = AccessMode.read)))
  assertBool "the retype declares the registry's state-level write (the sweep no footprint named)"
    ((lockSet_lifecycleRetype ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
        (ObjId.ofNat 30) none).pairs.any (fun p =>
      decide (p.fst = stateLevelLock ∧ p.snd = AccessMode.write)))
  -- The pin is that no two registry writers can hold disjoint sets.
  assertBool "no two registry writers have disjoint footprints"
    (decide (((lockSet_serviceRegister ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)).pairs.map (·.fst)).any
        (fun l => ((lockSet_lifecycleRetype ⟨6⟩ (ObjId.ofNat 11) (ObjId.ofNat 21)
          (ObjId.ofNat 31) none).pairs.map (·.fst)).contains l)))
  assertBool "the resolved retype footprint carries the target's own write lock"
    ((lockSet_lifecycleRetype ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20) (ObjId.ofNat 30)
        (some (notificationLock (ObjId.ofNat 40)))).pairs.any (fun p =>
      decide (p.fst = notificationLock (ObjId.ofNat 40) ∧ p.snd = AccessMode.write)))
  -- Audit-pass-3: .tcbSuspend now includes .schedContext (donation-cancel).
  -- WS-SM SM6.E: + .reply (the `.blockedOnReply` reply-link teardown).
  -- WS-OD OD3.5: `.objStore` — a suspend that cancels a donation maintains
  -- `SystemState.scThreadIndex`, an `RHTable` whose insert may rehash.
  assertBool "permittedKinds .tcbSuspend"
    (decide (permittedKinds .tcbSuspend =
      [.tcb, .cnode, .endpoint, .notification, .schedContext, .reply, .objStore]))
  -- WS-RR RR7.38: `.endpoint` and `.notification` — the queue owner's lock, on
  -- every arm that can write a queued TCB.
  -- WS-OD OD3.5: `.objStore` — the bind and the unbind maintain
  -- `SystemState.scThreadIndex`, an `RHTable` whose insert may rehash.
  assertBool "permittedKinds .schedContextBind"
    (decide (permittedKinds .schedContextBind =
      [.tcb, .cnode, .schedContext, .endpoint, .notification, .objStore]))
  -- Audit-pass-3: .call, .reply, .replyRecv include .schedContext (donation).
  -- WS-SM SM6.D: they also include .reply (per-object reply write-lock).
  -- WS-RR RR7.7: and `.objStore`, for the same CDT write `.send` declares.
  assertBool "permittedKinds .call (donation + reply-object + CDT kinds)"
    (decide (permittedKinds .call
      = [.tcb, .cnode, .endpoint, .schedContext, .reply, .objStore]))
  -- WS-OD OD3.5: `.objStore` — the donation return maintains `scThreadIndex`.
  assertBool "permittedKinds .reply (donation-return + reply-object + index kinds)"
    (decide (permittedKinds .reply = [.tcb, .cnode, .schedContext, .reply, .objStore]))
  assertBool "permittedKinds .replyRecv (donation-return + reply-object kind)"
    (decide (permittedKinds .replyRecv =
      [.tcb, .cnode, .endpoint, .schedContext, .reply, .objStore]))
  -- Audit-pass-6: .tcbSetPriority / .tcbSetMCPriority include .schedContext.
  -- updatePrioritySource writes the bound SC if binding is .bound/.donated.
  assertBool "permittedKinds .tcbSetPriority (audit-pass-6: includes .schedContext)"
    (decide (permittedKinds .tcbSetPriority =
      [.tcb, .cnode, .schedContext, .endpoint, .notification]))
  assertBool "permittedKinds .tcbSetMCPriority (audit-pass-6: includes .schedContext)"
    (decide (permittedKinds .tcbSetMCPriority =
      [.tcb, .cnode, .schedContext, .endpoint, .notification]))
  -- Audit-pass-6: .tcbSetIPCBuffer includes .vspaceRoot.
  -- validateIpcBufferAddress reads the target's VSpaceRoot.
  assertBool "permittedKinds .tcbSetIPCBuffer (audit-pass-6: includes .vspaceRoot)"
    (decide (permittedKinds .tcbSetIPCBuffer =
      [.tcb, .cnode, .vspaceRoot, .endpoint, .notification]))
  -- Audit-pass-6: .serviceRegister includes .endpoint.
  -- registerService reads st.objects[epId]? to verify endpoint kind.
  assertBool "permittedKinds .serviceRegister (audit-pass-6 .endpoint + the registry's state-level lock)"
    (decide (permittedKinds .serviceRegister = [.tcb, .cnode, .endpoint, .objStore]))
  assertBool "permittedKinds .serviceRevoke (registry mutation, under the state-level lock)"
    (decide (permittedKinds .serviceRevoke = [.tcb, .cnode, .objStore]))
  assertBool "permittedKinds .serviceQuery (registry lookup, under the state-level lock)"
    (decide (permittedKinds .serviceQuery = [.tcb, .cnode, .objStore]))

private def runLockKindHelpersChecks : IO Unit := do
  IO.println "--- §5 LockKind helpers ---"
  assertBool "tcbLock kind = .tcb"
    (decide ((tcbLock ⟨1⟩).kind = .tcb))
  assertBool "cnodeLock kind = .cnode"
    (decide ((cnodeLock (ObjId.ofNat 7)).kind = .cnode))
  assertBool "endpointLock kind = .endpoint"
    (decide ((endpointLock (ObjId.ofNat 20)).kind = .endpoint))
  assertBool "notificationLock kind = .notification"
    (decide ((notificationLock (ObjId.ofNat 30)).kind = .notification))
  assertBool "schedContextLock kind = .schedContext"
    (decide ((schedContextLock ⟨5⟩).kind = .schedContext))
  assertBool "vspaceRootLock kind = .vspaceRoot"
    (decide ((vspaceRootLock (ObjId.ofNat 99)).kind = .vspaceRoot))
  assertBool "untypedLock kind = .untyped"
    (decide ((untypedLock (ObjId.ofNat 200)).kind = .untyped))

private def runLockIdProjectionChecks : IO Unit := do
  IO.println "--- §6 LockId projection ---"
  -- KernelObject lockKind cases.
  let ep : Endpoint := {}
  assertBool "KernelObject.lockKind on endpoint = .endpoint"
    (decide ((KernelObject.endpoint ep).lockKind = .endpoint))
  let u : UntypedObject :=
    { regionBase := PAddr.ofNat 0, regionSize := 4096 }
  assertBool "KernelObject.lockKind on untyped = .untyped"
    (decide ((KernelObject.untyped u).lockKind = .untyped))
  -- LockId.fromObject pairs kind with ObjId.
  let oid := ObjId.ofNat 5
  assertBool "LockId.fromObject pairs kind + ObjId"
    (decide (LockId.fromObject oid (KernelObject.endpoint ep) = ⟨.endpoint, oid⟩))
  -- LockId.lookup on default SystemState is none.
  assertBool "LockId.lookup default state at tcb 1 = none"
    (decide (LockId.lookup (default : SystemState) ⟨.tcb, ObjId.ofNat 1⟩ = none))
  assertBool "LockId.lookup default state at endpoint 99 = none"
    (decide (LockId.lookup (default : SystemState) ⟨.endpoint, ObjId.ofNat 99⟩ = none))

private def runPerTransitionShapeChecks : IO Unit := do
  IO.println "--- §7 Per-transition lock-set shapes ---"
  -- IPC: send without receiver = 3 locks; with receiver = 4.
  assertBool "endpointSend size (no receiver) = 3"
    (decide ((lockSet_endpointSend ⟨1⟩ (ObjId.ofNat 10) (ObjId.ofNat 20) none).size = 3))
  assertBool "endpointSend size (with receiver) = 4"
    (decide ((lockSet_endpointSend ⟨1⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
              (some ⟨2⟩)).size = 4))
  -- Capability paths: 4 locks each since WS-RR RR7.9 — three per-object members
  -- plus the state-level write the CDT mutation needs.
  assertBool "cspaceMint size = 4"
    (decide ((lockSet_cspaceMint ⟨1⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)).size = 4))
  assertBool "cspaceMove size = 4"
    (decide ((lockSet_cspaceMove ⟨1⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)).size = 4))
  -- …and the member is present in all four, which the size alone would not say.
  assertBool "every capability operation declares the state-level CDT write"
    (decide ((stateLevelLock, AccessMode.write)
        ∈ (lockSet_cspaceMint ⟨1⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)).pairs) &&
     decide ((stateLevelLock, AccessMode.write)
        ∈ (lockSet_cspaceCopy ⟨1⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)).pairs) &&
     decide ((stateLevelLock, AccessMode.write)
        ∈ (lockSet_cspaceMove ⟨1⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)).pairs) &&
     decide ((stateLevelLock, AccessMode.write)
        ∈ (lockSet_cspaceDelete ⟨1⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)).pairs) &&
     decide ((stateLevelLock, AccessMode.write)
        ∈ (lockSet_mintReplyCap ⟨1⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)).pairs))
  -- VSpace: 3 locks each.
  assertBool "vspaceMap size = 3"
    (decide ((lockSet_vspaceMap ⟨1⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)).size = 3))
  -- Lifecycle: 5 locks (caller TCB read + CNode root read + untyped write + dst
  -- CNode write + the state-level write WS-RR RR7.23 added for the registry
  -- sweep and the CDT detach the pre-retype cleanup performs).
  assertBool "lifecycleRetype size = 5"
    (decide ((lockSet_lifecycleRetype ⟨1⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
              (ObjId.ofNat 30)).size = 5))
  -- **WS-OD (`v0.35.4`)**: the suspend's optional members, at the two footprints
  -- that own them since the parametric `lockSet_tcbSuspend` was retired.
  -- Teardown with both blocked objects: victim + endpoint + notification.
  assertBool "cancelIpcBlocking size (block-options some, no donation) = 3"
    (decide ((SeLe4n.Kernel.lockSet_cancelIpcBlocking ⟨3⟩
              (some (ObjId.ofNat 20)) (some (ObjId.ofNat 30)) none none none none
              (none, none) none none none none).size = 3))
  -- Teardown with no options: the victim alone.
  assertBool "cancelIpcBlocking size (no Options) = 1"
    (decide ((SeLe4n.Kernel.lockSet_cancelIpcBlocking ⟨3⟩ none none none none none none
              (none, none) none none none none).size = 1))
  -- Donation cancellation of a `.bound` binding: victim + SC + index.
  -- **WS-OD OD3.5**: the state-level lock, because `scThreadIndex` is an
  -- `RHTable` no per-object lock decomposes.
  assertBool "cancelDonation size (.bound binding, SC + index) = 3"
    (decide ((SeLe4n.Kernel.lockSet_cancelDonation ⟨3⟩ (some ⟨50⟩) none
              none none none).size = 3))
  assertBool "a SchedContext-resolving donation cancellation declares the state-level lock"
    (decide ((stateLevelLock, AccessMode.write)
      ∈ (SeLe4n.Kernel.lockSet_cancelDonation ⟨3⟩ (some ⟨50⟩) none
           none none none).pairs))
  -- …of a `.donated` binding: + the original owner.
  assertBool "cancelDonation size (.donated binding, SC + originalOwner + index) = 4"
    (decide ((SeLe4n.Kernel.lockSet_cancelDonation ⟨3⟩ (some ⟨50⟩) (some ⟨7⟩)
              none none none).size = 4))
  -- **WS-OD (`v0.35.4`)**: …and the pop the donated arm performs — the head it
  -- clears, the frame below it re-heads and the outer caller it validates.
  assertBool "cancelDonation size (.donated + the pop's three stack objects) = 7"
    (decide ((SeLe4n.Kernel.lockSet_cancelDonation ⟨3⟩ (some ⟨50⟩) (some ⟨7⟩)
              (some ⟨60⟩) (some ⟨61⟩) (some ⟨9⟩)).size = 7))
  -- The widest teardown arm: a reply-arm victim owed a donation whose holder is
  -- itself blocked, at reply-stack depth ≥ 3.
  assertBool "cancelIpcBlocking size (full: every member some) = 14"
    (decide ((SeLe4n.Kernel.lockSet_cancelIpcBlocking ⟨3⟩
              (some (ObjId.ofNat 20)) (some (ObjId.ofNat 30)) (some ⟨60⟩)
              (some ⟨50⟩) (some ⟨7⟩) (some (ObjId.ofNat 21))
              (some ⟨8⟩, some ⟨9⟩) (some ⟨61⟩) (some ⟨11⟩)
              (some ⟨62⟩) (some ⟨63⟩)).size = 14))
  -- Audit-pass-6 P1: tcbSetPriority with unbound target = 3 locks
  -- (caller TCB read, CNode read, target TCB write — no SC).
  assertBool "tcbSetPriority size (unbound target, no SC) = 3"
    (decide ((lockSet_tcbSetPriority ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩ none none).size = 3))
  -- Audit-pass-6 P1: tcbSetPriority with bound SC = 4 locks.
  assertBool "tcbSetPriority size (.bound binding, SC included) = 4"
    (decide ((lockSet_tcbSetPriority ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩ (some ⟨50⟩) none).size = 4))
  -- Audit-pass-6 P1: tcbSetMCPriority with unbound target = 3 locks.
  assertBool "tcbSetMCPriority size (unbound target, no SC) = 3"
    (decide ((lockSet_tcbSetMCPriority ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩ none none).size = 3))
  -- Audit-pass-6 P1: tcbSetMCPriority with bound SC = 4 locks.
  assertBool "tcbSetMCPriority size (.bound binding, SC included) = 4"
    (decide ((lockSet_tcbSetMCPriority ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩ (some ⟨50⟩) none).size = 4))
  -- Audit-pass-6 P1: tcbSetIPCBuffer with no target VSpaceRoot (target absent) = 3 locks.
  assertBool "tcbSetIPCBuffer size (no VSpaceRoot) = 3"
    (decide ((lockSet_tcbSetIPCBuffer ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩ none none).size = 3))
  -- Audit-pass-6 P1: tcbSetIPCBuffer with target VSpaceRoot = 4 locks.
  assertBool "tcbSetIPCBuffer size (VSpaceRoot included) = 4"
    (decide ((lockSet_tcbSetIPCBuffer ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩
              (some (ObjId.ofNat 99)) none).size = 4))
  -- Audit-pass-6 P2: serviceRegister takes a mandatory endpoint read lock;
  -- WS-RR RR7.23 added the registry's own state-level write.
  assertBool "serviceRegister size (endpoint + the registry's state-level write) = 4"
    (decide ((lockSet_serviceRegister ⟨1⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)).size = 4))
  assertBool "serviceRevoke size (caller, root, registry) = 3"
    (decide ((lockSet_serviceRevoke ⟨1⟩ (ObjId.ofNat 10)).size = 3))
  assertBool "serviceQuery size (caller, root, registry) = 3"
    (decide ((lockSet_serviceQuery ⟨1⟩ (ObjId.ofNat 10)).size = 3))

private def runLubMergeChecks : IO Unit := do
  IO.println "--- §9 Lub-merging on duplicate keys ---"
  -- read + write at same key → write
  let s1 := LockSet.empty.insertOrMerge ⟨.tcb, ObjId.ofNat 5⟩ .read
              |>.insertOrMerge ⟨.tcb, ObjId.ofNat 5⟩ .write
  assertBool "insertOrMerge read+write at same key gives single (write) entry"
    (decide (s1.size = 1 ∧ s1.pairs = [(⟨.tcb, ObjId.ofNat 5⟩, .write)]))
  -- write + read at same key → write (commutativity of lub)
  let s2 := LockSet.empty.insertOrMerge ⟨.tcb, ObjId.ofNat 5⟩ .write
              |>.insertOrMerge ⟨.tcb, ObjId.ofNat 5⟩ .read
  assertBool "insertOrMerge write+read at same key gives single (write) entry"
    (decide (s2.size = 1 ∧ s2.pairs = [(⟨.tcb, ObjId.ofNat 5⟩, .write)]))
  -- read + read at same key → read
  let s3 := LockSet.empty.insertOrMerge ⟨.tcb, ObjId.ofNat 5⟩ .read
              |>.insertOrMerge ⟨.tcb, ObjId.ofNat 5⟩ .read
  assertBool "insertOrMerge read+read at same key gives single (read) entry"
    (decide (s3.pairs = [(⟨.tcb, ObjId.ofNat 5⟩, .read)]))
  -- Self-suspend (callerTid = targetTcbTid) collapses TCB locks.
  let selfSuspend := SeLe4n.Kernel.lockSet_tcbSuspendOnCore default ⟨5⟩ (ObjId.ofNat 10) ⟨5⟩
  assertBool "tcbSuspend(caller=target) collapses to 2 locks (cnode + merged TCB)"
    (decide (selfSuspend.size = 2))
  assertBool "tcbSuspend(caller=target) merged TCB lock is write"
    (decide (selfSuspend.lockAcquireSequence =
      [(⟨.cnode, ObjId.ofNat 10⟩, .read),
       (⟨.tcb, ObjId.ofNat 5⟩, .write)]))
  -- endpointReply(caller=replyTarget) collapses.
  let selfReply := lockSet_endpointReply ⟨5⟩ (ObjId.ofNat 10) ⟨5⟩ none none none none none
  assertBool "endpointReply(caller=replyTarget) collapses to 2 locks"
    (decide (selfReply.size = 2))
  -- Audit-pass-3+4: endpointReply with donation-return.
  -- Under invariant, originalOwner == replyTarget so the duplicate TCB
  -- entry collapses via lub-merge — 4 locks total.
  -- WS-OD OD3.5: five, not four — a reply that returns a donation also holds
  -- the state-level lock, for the `scThreadIndex` maintenance the return ends in.
  let donReply := lockSet_endpointReply ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩
                    (some ⟨42⟩) (some ⟨7⟩) none none none
  assertBool "endpointReply(caller=5, target=7, donatedSc=42, owner=7=target) has 5 locks (lub-collapse)"
    (decide (donReply.size = 5))
  -- Audit-pass-4: under hypothetical invariant violation where
  -- originalOwner ≠ replyTarget, the lockSet correctly covers both.
  let donReplyDrift := lockSet_endpointReply ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩
                         (some ⟨42⟩) (some ⟨9⟩) none none none
  assertBool "endpointReply(caller=5, target=7, owner=9≠target) has 6 locks (drift case)"
    (decide (donReplyDrift.size = 6))
  -- WS-OD OD3.5: a reply that returns *nothing* holds no state-level lock — the
  -- member is conditioned on the donation, not unconditional, and a check that
  -- only ever saw the donating shape could not tell the two apart.
  let bareReply := lockSet_endpointReply ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩ none none none none none
  assertBool "endpointReply with no donation has 3 locks (no state-level member)"
    (decide (bareReply.size = 3))
  -- Audit-pass-3+4: replyRecv with full donation extension.
  -- WS-OD OD3.5: seven, not six — the state-level lock joins for the same reason.
  let donReplyRecv := lockSet_replyRecv ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩
                       (ObjId.ofNat 20) (some ⟨8⟩) (some ⟨42⟩) (some ⟨7⟩) none false
                       none none none none
  assertBool "replyRecv (sender + donation + owner=target=7 collapse) has 7 locks"
    (decide (donReplyRecv.size = 7))
  -- WS-OD OD3.5: a **non-delegated** reply names its recorded server, and that
  -- is the invoking thread, so the member merges and the size does not move.
  let selfServedReplyRecv := lockSet_replyRecv ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩
                              (ObjId.ofNat 20) (some ⟨8⟩) (some ⟨42⟩) (some ⟨7⟩) none false
                              (some ⟨5⟩) none none none
  assertBool "replyRecv with a non-delegated recorded server still has 7 locks (lub-collapse)"
    (decide (selfServedReplyRecv.size = 7))
  -- ...and a **delegated** one names a third thread, which is the member PR #892
  -- review round 6 had no room for and OD3.5 declares.
  let delegatedReplyRecv := lockSet_replyRecv ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩
                             (ObjId.ofNat 20) (some ⟨8⟩) (some ⟨42⟩) (some ⟨7⟩) none false
                             (some ⟨9⟩) none none none
  assertBool "replyRecv with a delegated recorded server has 8 locks"
    (decide (delegatedReplyRecv.size = 8))
  -- ...and the second SchedContext hand-off — the member whose absence made this
  -- footprint false — is a ninth, distinct from the returned context.
  let redonatingReplyRecv := lockSet_replyRecv ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩
                              (ObjId.ofNat 20) (some ⟨8⟩) (some ⟨42⟩) (some ⟨7⟩) none false
                              (some ⟨9⟩) (some ⟨43⟩) none none
  assertBool "replyRecv that also re-donates has 9 locks (the second hand-off's SC)"
    (decide (redonatingReplyRecv.size = 9))
  -- WS-OD OD3.7: and the two objects the donation return reads *below* the
  -- reply-stack head are a twelfth and thirteenth — the reason the ceiling moved
  -- again.  Each is asserted on its own, since a member that merged would make
  -- the raise look unnecessary while the footprint stayed false.
  let belowHeadReplyRecv := lockSet_replyRecv ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩
                             (ObjId.ofNat 20) (some ⟨8⟩) (some ⟨42⟩) (some ⟨7⟩) none false
                             (some ⟨9⟩) (some ⟨43⟩) (some ⟨44⟩) none
  assertBool "replyRecv that reads the Reply below the head has 10 locks"
    (decide (belowHeadReplyRecv.size = 10))
  let outerCallerReplyRecv := lockSet_replyRecv ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩
                               (ObjId.ofNat 20) (some ⟨8⟩) (some ⟨42⟩) (some ⟨7⟩) none false
                               (some ⟨9⟩) (some ⟨43⟩) none (some ⟨12⟩)
  assertBool "replyRecv that also validates the outer caller's TCB has 10 locks"
    (decide (outerCallerReplyRecv.size = 10))
  -- The widest shape the arm can declare: a delegated, re-donating, caps-carrying
  -- `.replyRecv` with a distinct original owner, reaching both objects below its
  -- reply-stack head, relinking the queue-structure TCB its receive leg writes
  -- (WS-OD OD3.13), WS-OD (`v0.35.4`)'s head its pop clears and old head its
  -- re-donation's push rewrites, and — PR #894's review — the five objects the
  -- INVOKING receiver's own pre-receive return touches: twenty-one, which is
  -- what `maxLockSetSize` is measured against.
  let widestReplyRecv := lockSet_replyRecv ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩
                          (ObjId.ofNat 20) (some ⟨8⟩) (some ⟨42⟩) (some ⟨11⟩)
                          (some ⟨60⟩) true (some ⟨9⟩) (some ⟨43⟩)
                          (some ⟨44⟩) (some ⟨12⟩) (some ⟨13⟩)
                          (some ⟨45⟩) (some ⟨46⟩)
                          (some ⟨47⟩) (some ⟨14⟩) (some ⟨48⟩) (some ⟨49⟩)
                          (some ⟨15⟩)
  assertBool "the widest declarable .replyRecv has 21 locks (= maxLockSetSize)"
    (decide (widestReplyRecv.size = 21))
  assertBool "...and that is exactly maxLockSetSize"
    (decide (widestReplyRecv.size = maxLockSetSize))
  -- **PR #894 review**: and no *reachable* state declares all twenty-one --
  -- the re-donation members are live exactly when the endpoint has a queued
  -- sender and the invoker's pre-receive return exactly when it does not.  The
  -- widest reachable no-sender shape is eighteen; the widest rendezvous shape is
  -- sixteen.  Both are exercised here at the same operands so the difference is
  -- attributable to the mutual exclusion and nothing else.
  let blockingReplyRecv := lockSet_replyRecv ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩
                            (ObjId.ofNat 20) none (some ⟨42⟩) (some ⟨11⟩)
                            (some ⟨60⟩) true (some ⟨9⟩) none
                            (some ⟨44⟩) (some ⟨12⟩) (some ⟨13⟩)
                            none (some ⟨46⟩)
                            (some ⟨47⟩) (some ⟨14⟩) (some ⟨48⟩) (some ⟨49⟩)
                            (some ⟨15⟩)
  assertBool "the widest reachable blocking .replyRecv has 18 locks"
    (decide (blockingReplyRecv.size = 18))
  let rendezvousReplyRecv := lockSet_replyRecv ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩
                              (ObjId.ofNat 20) (some ⟨8⟩) (some ⟨42⟩) (some ⟨11⟩)
                              (some ⟨60⟩) true (some ⟨9⟩) (some ⟨43⟩)
                              (some ⟨44⟩) (some ⟨12⟩) (some ⟨13⟩)
                              (some ⟨45⟩) (some ⟨46⟩)
                              none none none none none
  assertBool "the widest reachable rendezvous .replyRecv has 16 locks"
    (decide (rendezvousReplyRecv.size = 16))
  -- NEGATIVE: neither reachable shape reaches the ceiling, which is the whole
  -- content of `lockSet_endpointReplyRecvOnCore_size_le_eighteen` -- a witness
  -- asserting only `≤ maxLockSetSize` would pass with the slack claim false.
  assertBool "NEGATIVE: no reachable .replyRecv shape reaches maxLockSetSize"
    (!decide (blockingReplyRecv.size = maxLockSetSize
              || rendezvousReplyRecv.size = maxLockSetSize))

private def runUnionChecks : IO Unit := do
  IO.println "--- §10 LockSet.union semantics ---"
  let s1 := LockSet.singleton ⟨.tcb, ObjId.ofNat 1⟩ .write
  let s2 := LockSet.singleton ⟨.endpoint, ObjId.ofNat 2⟩ .write
  assertBool "union of disjoint LockSets has size 2"
    (decide ((s1.union s2).size = 2))
  let s3 := LockSet.singleton ⟨.tcb, ObjId.ofNat 1⟩ .read
  let s4 := LockSet.singleton ⟨.tcb, ObjId.ofNat 1⟩ .write
  assertBool "union of overlapping LockSets merges via lub"
    (decide ((s3.union s4).pairs = [(⟨.tcb, ObjId.ofNat 1⟩, .write)]))
  assertBool "union with empty is identity"
    (decide (s1.union LockSet.empty = s1))

private def runConsistencyRuntimeChecks : IO Unit := do
  IO.println "--- §11 Runtime exercise of lockSet_consistent_* ---"
  -- Build a concrete LockSet via lockSet_endpointSend and verify EVERY
  -- entry's kind is in permittedKinds .send.
  let send := lockSet_endpointSend ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20) (some ⟨8⟩)
  let allOk_send := send.pairs.all (fun p =>
    decide (p.fst.kind ∈ permittedKinds .send))
  assertBool "lockSet_endpointSend (with receiver): all kinds in permittedKinds .send"
    allOk_send
  -- **WS-OD (`v0.35.4`)**: the `.tcbSuspend` kinds, at the teardown footprint the
  -- suspend footprint is built over, with every optional member `some`.
  let susp := SeLe4n.Kernel.lockSet_cancelIpcBlocking ⟨3⟩
                (some (ObjId.ofNat 20)) (some (ObjId.ofNat 30)) (some ⟨60⟩)
                (some ⟨50⟩) (some ⟨7⟩) (some (ObjId.ofNat 21))
                (some ⟨8⟩, some ⟨9⟩) (some ⟨61⟩) (some ⟨11⟩)
                (some ⟨62⟩) (some ⟨63⟩)
  let allOk_susp := susp.pairs.all (fun p =>
    decide (p.fst.kind ∈ permittedKinds .tcbSuspend))
  assertBool "lockSet_cancelIpcBlocking (every Option some): all kinds in permittedKinds .tcbSuspend"
    allOk_susp
  -- **WS-RR RR7.7**: the capability-transfer destination is *declared*, not
  -- merely admissible.  A consistency check asks whether every declared kind is
  -- permitted, which a footprint that declares nothing also passes; these ask
  -- whether the two members the transfer needs are in the set at all.
  let sendCaps := lockSet_endpointSend ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
                    (some ⟨8⟩) (some (ObjId.ofNat 42))
  assertBool "send with caps declares the receiver CSpace root in write mode"
    (sendCaps.pairs.contains (cnodeLock (ObjId.ofNat 42), AccessMode.write))
  assertBool "send with caps declares the state-level lock for the CDT write"
    (sendCaps.pairs.contains (stateLevelLock, AccessMode.write))
  let callCaps := lockSet_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
                    (some ⟨8⟩) (some ⟨100⟩) (some ⟨7⟩) (some (ObjId.ofNat 42))
  assertBool "call with caps declares the receiver CSpace root in write mode"
    (callCaps.pairs.contains (cnodeLock (ObjId.ofNat 42), AccessMode.write))
  assertBool "call with caps declares the state-level lock for the CDT write"
    (callCaps.pairs.contains (stateLevelLock, AccessMode.write))
  -- …and the capless shape declares neither, so the members are the transfer's
  -- rather than an unconditional widening of every IPC footprint.
  let sendCapless := lockSet_endpointSend ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
                       (some ⟨8⟩)
  assertBool "a capless send declares no state-level lock"
    (!sendCapless.pairs.contains (stateLevelLock, AccessMode.write))
  -- The destination coinciding with the caller's own root upgrades the existing
  -- read rather than adding a member: same size, stronger mode.
  let sendSameRoot := lockSet_endpointSend ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
                        (some ⟨8⟩) (some (ObjId.ofNat 10))
  assertBool "a transfer into the caller's own CSpace upgrades the read, not the size"
    (decide (sendSameRoot.size = sendCapless.size + 1)
      && sendSameRoot.pairs.contains (cnodeLock (ObjId.ofNat 10), AccessMode.write))
  -- Edge case: no Option args.
  let mint := lockSet_cspaceMint ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
  let allOk_mint := mint.pairs.all (fun p =>
    decide (p.fst.kind ∈ permittedKinds .cspaceMint))
  assertBool "lockSet_cspaceMint: all kinds in permittedKinds .cspaceMint"
    allOk_mint
  -- 4-base-arg transition.
  let retype := lockSet_lifecycleRetype ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
                  (ObjId.ofNat 30)
  let allOk_retype := retype.pairs.all (fun p =>
    decide (p.fst.kind ∈ permittedKinds .lifecycleRetype))
  assertBool "lockSet_lifecycleRetype: all kinds in permittedKinds .lifecycleRetype"
    allOk_retype
  -- Audit-pass-3: donation extension on .call.
  let callDon := lockSet_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
                   (some ⟨8⟩) (some ⟨100⟩)
  let allOk_callDon := callDon.pairs.all (fun p =>
    decide (p.fst.kind ∈ permittedKinds .call))
  assertBool "lockSet_endpointCall (with donation): all kinds in permittedKinds .call"
    allOk_callDon
  -- Audit-pass-3+4: donation-return extension on .reply (full args).
  -- WS-OD OD3.7: taken with both below-head reads resolved, so the kind check
  -- covers the shape the live arm declares at call depth ≥ 2 rather than the
  -- chain-free one.
  let replyDon := lockSet_endpointReply ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩
                    (some ⟨42⟩) (some ⟨7⟩) none (some ⟨44⟩) (some ⟨12⟩)
  let allOk_replyDon := replyDon.pairs.all (fun p =>
    decide (p.fst.kind ∈ permittedKinds .reply))
  assertBool "lockSet_endpointReply (with donation + owner): all kinds in permittedKinds .reply"
    allOk_replyDon
  -- Audit-pass-6 P1: .tcbSetPriority with bound SC — every kind permitted.
  let setPriBound := lockSet_tcbSetPriority ⟨5⟩ (ObjId.ofNat 10) ⟨3⟩ (some ⟨50⟩) none
  let allOk_setPriBound := setPriBound.pairs.all (fun p =>
    decide (p.fst.kind ∈ permittedKinds .tcbSetPriority))
  assertBool "lockSet_tcbSetPriority (.bound binding, SC included): all kinds permitted"
    allOk_setPriBound
  -- Audit-pass-6 P1: .tcbSetMCPriority with bound SC.
  let setMcpBound := lockSet_tcbSetMCPriority ⟨5⟩ (ObjId.ofNat 10) ⟨3⟩ (some ⟨50⟩) none
  let allOk_setMcpBound := setMcpBound.pairs.all (fun p =>
    decide (p.fst.kind ∈ permittedKinds .tcbSetMCPriority))
  assertBool "lockSet_tcbSetMCPriority (.bound binding, SC included): all kinds permitted"
    allOk_setMcpBound
  -- Audit-pass-6 P1: .tcbSetIPCBuffer with VSpaceRoot.
  let setIpcVsr := lockSet_tcbSetIPCBuffer ⟨5⟩ (ObjId.ofNat 10) ⟨3⟩
                     (some (ObjId.ofNat 99)) none
  let allOk_setIpcVsr := setIpcVsr.pairs.all (fun p =>
    decide (p.fst.kind ∈ permittedKinds .tcbSetIPCBuffer))
  assertBool "lockSet_tcbSetIPCBuffer (VSpaceRoot included): all kinds permitted"
    allOk_setIpcVsr
  -- Audit-pass-6 P2: .serviceRegister with endpoint.
  let svcReg := lockSet_serviceRegister ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
  let allOk_svcReg := svcReg.pairs.all (fun p =>
    decide (p.fst.kind ∈ permittedKinds .serviceRegister))
  assertBool "lockSet_serviceRegister (with endpoint): all kinds permitted"
    allOk_svcReg

/-- **WS-RR RR7.38**: the queue-owner member — the declaration that closed
`UncoveredLockDomain.queueOwnershipProtocol`.

The fixtures above pass `none` and so still say exactly what they said, because
`lockSetExtendOpt _ none` is the identity.  These say what the parameter is
*for*: at `some`, the owner's write lock is a member, the footprint is one wider,
and its kind is admitted.  Without them the widening would be a parameter every
call site passes `none` to — a member no test ever sees. -/
private def runQueueOwnerFootprintChecks : IO Unit := do
  IO.println "--- §18 WS-RR RR7.38 queue-owner footprint member ---"
  let ep : QueueOwner := .endpoint (ObjId.ofNat 20)
  let ntfn : QueueOwner := .notification (ObjId.ofNat 21)
  let bare := lockSet_tcbSetPriority ⟨5⟩ (ObjId.ofNat 10) ⟨3⟩ (some ⟨50⟩) none
  let queuedEp := lockSet_tcbSetPriority ⟨5⟩ (ObjId.ofNat 10) ⟨3⟩ (some ⟨50⟩) (some ep)
  let queuedNtfn := lockSet_tcbSetPriority ⟨5⟩ (ObjId.ofNat 10) ⟨3⟩ (some ⟨50⟩) (some ntfn)
  assertBool "a queued target adds exactly one member"
    (decide (queuedEp.size = bare.size + 1))
  assertBool "…and that member is the endpoint's WRITE lock, not a read"
    (queuedEp.pairs.any (fun p =>
      decide (p = (⟨.endpoint, ObjId.ofNat 20⟩, AccessMode.write))))
  assertBool "NEGATIVE: at `none` the footprint carries no endpoint lock at all"
    (decide (bare.pairs.all (fun p => p.fst.kind ≠ .endpoint)))
  assertBool "a notification-queued target contributes the notification lock instead"
    (queuedNtfn.pairs.any (fun p =>
      decide (p = (⟨.notification, ObjId.ofNat 21⟩, AccessMode.write))))
  -- The kinds the widened arm admits are exactly the two a queue owner can be.
  assertBool "the queue-owner member's kind is permitted on the widened arm"
    (queuedEp.pairs.all (fun p => decide (p.fst.kind ∈ permittedKinds .tcbSetPriority))
     && queuedNtfn.pairs.all (fun p => decide (p.fst.kind ∈ permittedKinds .tcbSetPriority)))
  -- The resolver: a blocked thread has an owner, a ready one does not.
  let baseTcb : TCB :=
    { tid := ThreadId.ofNat 3, priority := ⟨10⟩, domain := ⟨0⟩,
      cspaceRoot := ObjId.ofNat 0, vspaceRoot := ObjId.ofNat 0,
      ipcBuffer := SeLe4n.VAddr.ofNat 0 }
  let blockedTcb : TCB := { baseTcb with ipcState := .blockedOnSend (ObjId.ofNat 20) }
  let readyTcb : TCB := { baseTcb with ipcState := .ready }
  assertBool "queueOwnerOf? reads the owner off a blocked thread's ipcState"
    (decide (queueOwnerOf? blockedTcb = some (.endpoint (ObjId.ofNat 20))))
  assertBool "NEGATIVE: a ready thread is in no object-owned queue"
    (decide (queueOwnerOf? readyTcb = none))

/-- **WS-OD OD4.7 / OD6.3**: the `.call` footprint already declares every object
the donation **push** writes, which is why the chain costs no ceiling.

`donateSchedContext` writes **five** keys since the reply stack became doubly
linked (WS-OD `v0.35.4`) -- the donated SchedContext (rebind *and* new stack
head, one store), the pushed Reply (`prev := oldHead?`, `next := .head scId`),
the **old head** the push links down to (`next := .frame pushRid`), the donor's
TCB (`.unbound`) and the receiver's TCB (`.donated`) -- and each is a declared
WRITE member here.  Relation, not presence: the negative keeps every other
member and removes the *resolver's answer*, which is what a footprint that
failed to resolve the donation would look like, and the size check is stated
against `maxLockSetSize` rather than against a numeral (WS-OD OD3.19's rule:
a figure interpolated from the constant cannot drift away from it). -/
private def runDonationPushFootprintChecks : IO Unit := do
  IO.println "--- §19 WS-OD OD4.7 the `.call` footprint covers the donation push ---"
  let caller : ThreadId := ⟨5⟩
  let receiver : ThreadId := ⟨6⟩
  let scId : SchedContextId := ⟨70⟩
  let rid : ReplyId := ⟨71⟩
  let oldHead : ReplyId := ⟨72⟩
  let donating := lockSet_endpointCall caller (ObjId.ofNat 10) (ObjId.ofNat 20)
    (some receiver) (some scId) (some rid) none none (some oldHead)
  let undonating := lockSet_endpointCall caller (ObjId.ofNat 10) (ObjId.ofNat 20)
    (some receiver) none (some rid) none none none
  assertBool "the donated SchedContext is a declared WRITE member"
    (donating.pairs.any (fun p => decide (p = (schedContextLock scId, AccessMode.write))))
  assertBool "...so is the Reply the pushed frame IS"
    (donating.pairs.any (fun p => decide (p = (replyLock rid, AccessMode.write))))
  assertBool "...so is the receiver's TCB, which the push rebinds `.donated`"
    (donating.pairs.any (fun p => decide (p = (tcbLock receiver, AccessMode.write))))
  assertBool "...and the donor's own TCB, which the push leaves `.unbound`"
    (donating.pairs.any (fun p => decide (p = (tcbLock caller, AccessMode.write))))
  assertBool "...and (WS-OD `v0.35.4`) the old head the push links down to"
    (donating.pairs.any (fun p => decide (p = (replyLock oldHead, AccessMode.write))))
  assertBool "NEGATIVE: with no donation resolved the SchedContext lock is absent"
    (decide (undonating.pairs.all (fun p => p.fst.kind ≠ .schedContext)))
  IO.println s!"    declared ceiling: maxLockSetSize = {maxLockSetSize}"
  assertBool "the donating `.call` footprint fits the declared ceiling"
    (decide (donating.size ≤ maxLockSetSize))

/-- Audit-pass-6 P1/P2 runtime checks: per-syscall lock-set
correctness against the actual kernel transitions traced. -/
private def runAuditPass6FootprintChecks : IO Unit := do
  IO.println "--- §17 Audit-pass-6 footprint completeness (P1+P2 closure) ---"
  -- P1 (tcbSetPriority): with unbound target, no SC lock — but the
  -- bound case adds (schedContextLock scId, .write).
  let unboundPri := lockSet_tcbSetPriority ⟨5⟩ (ObjId.ofNat 10) ⟨3⟩ none none
  let boundPri := lockSet_tcbSetPriority ⟨5⟩ (ObjId.ofNat 10) ⟨3⟩ (some ⟨50⟩) none
  assertBool "P1: tcbSetPriority(.bound) has one more lock than .unbound"
    (decide (boundPri.size = unboundPri.size + 1))
  assertBool "P1: tcbSetPriority(.bound 50) contains schedContextLock ⟨50⟩ as write"
    (boundPri.pairs.any (fun p =>
      decide (p = (⟨.schedContext, ObjId.ofNat 50⟩, .write))))
  -- P1 (tcbSetMCPriority): same shape.
  let boundMcp := lockSet_tcbSetMCPriority ⟨5⟩ (ObjId.ofNat 10) ⟨3⟩ (some ⟨50⟩) none
  assertBool "P1: tcbSetMCPriority(.bound) contains schedContextLock ⟨50⟩ as write"
    (boundMcp.pairs.any (fun p =>
      decide (p = (⟨.schedContext, ObjId.ofNat 50⟩, .write))))
  -- P1 (tcbSetIPCBuffer): with target VSpaceRoot, contains read lock.
  let withVsr := lockSet_tcbSetIPCBuffer ⟨5⟩ (ObjId.ofNat 10) ⟨3⟩
                    (some (ObjId.ofNat 99)) none
  assertBool "P1: tcbSetIPCBuffer(some 99) contains vspaceRootLock 99 as read"
    (withVsr.pairs.any (fun p =>
      decide (p = (⟨.vspaceRoot, ObjId.ofNat 99⟩, .read))))
  assertBool "P1: tcbSetIPCBuffer(none) does NOT contain any vspaceRoot lock"
    (let noVsr := lockSet_tcbSetIPCBuffer ⟨5⟩ (ObjId.ofNat 10) ⟨3⟩ none none
     decide (noVsr.pairs.all (fun p => p.fst.kind ≠ .vspaceRoot)))
  -- P2 (serviceRegister): contains the endpoint read lock.
  let svcReg := lockSet_serviceRegister ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
  assertBool "P2: serviceRegister contains endpointLock 20 as read"
    (svcReg.pairs.any (fun p =>
      decide (p = (⟨.endpoint, ObjId.ofNat 20⟩, .read))))
  assertBool "serviceRegister has exactly 4 locks (tcb + cnode + endpoint + registry)"
    (decide (svcReg.size = 4))
  -- Canonical-sort cross-check: the new SC entries in tcbSetPriority
  -- sort AFTER the target TCB at the same hierarchy band but distinct
  -- ObjIds.  At hierarchy level: cnode=2, tcb=3, schedContext=7.  So the
  -- expected sort places the SC last.
  let boundPriSeq := boundPri.lockAcquireSequence
  assertBool "P1: tcbSetPriority(.bound 50) canonical sort places SC at end (level 7)"
    (decide (boundPriSeq.getLast? = some (⟨.schedContext, ObjId.ofNat 50⟩, .write)))
  -- Similarly for setIPCBuffer: VSpaceRoot at level 8, sorts last.
  let ipcSeq := withVsr.lockAcquireSequence
  assertBool "P1: tcbSetIPCBuffer(some 99) canonical sort places VSpaceRoot at end (level 8)"
    (decide (ipcSeq.getLast? = some (⟨.vspaceRoot, ObjId.ofNat 99⟩, .read)))
  -- P2 canonical: endpoint at level 4, sorts after cnode(2) but before tcb(3).
  -- Actually wait — hierarchy is cnode=2 < tcb=3 < endpoint=4.  So endpoint is last.
  let svcRegSeq := svcReg.lockAcquireSequence
  assertBool "P2: serviceRegister canonical sort places endpoint at end (level 4)"
    (decide (svcRegSeq.getLast? = some (⟨.endpoint, ObjId.ofNat 20⟩, .read)))

private def runCanonicalSortRuntimeChecks : IO Unit := do
  IO.println "--- §12 lockAcquireSequence canonical sort runtime ---"
  -- The sort is total and deterministic regardless of input order.
  -- Verify by constructing the same multiset in different orders and
  -- checking they produce the same lockAcquireSequence output.
  let order1 := LockSet.empty.insertOrMerge ⟨.endpoint, ObjId.ofNat 20⟩ .write
                  |>.insertOrMerge ⟨.tcb, ObjId.ofNat 5⟩ .write
                  |>.insertOrMerge ⟨.cnode, ObjId.ofNat 10⟩ .read
  let order2 := LockSet.empty.insertOrMerge ⟨.cnode, ObjId.ofNat 10⟩ .read
                  |>.insertOrMerge ⟨.endpoint, ObjId.ofNat 20⟩ .write
                  |>.insertOrMerge ⟨.tcb, ObjId.ofNat 5⟩ .write
  let order3 := LockSet.empty.insertOrMerge ⟨.tcb, ObjId.ofNat 5⟩ .write
                  |>.insertOrMerge ⟨.cnode, ObjId.ofNat 10⟩ .read
                  |>.insertOrMerge ⟨.endpoint, ObjId.ofNat 20⟩ .write
  let expected : List (LockId × AccessMode) :=
    [(⟨.cnode, ObjId.ofNat 10⟩, .read),
     (⟨.tcb, ObjId.ofNat 5⟩, .write),
     (⟨.endpoint, ObjId.ofNat 20⟩, .write)]
  assertBool "lockAcquireSequence: order1 produces canonical output"
    (decide (order1.lockAcquireSequence = expected))
  assertBool "lockAcquireSequence: order2 produces canonical output"
    (decide (order2.lockAcquireSequence = expected))
  assertBool "lockAcquireSequence: order3 produces canonical output"
    (decide (order3.lockAcquireSequence = expected))
  -- Within-kind sort: ObjIds ascending.
  let withinKind := LockSet.empty.insertOrMerge ⟨.tcb, ObjId.ofNat 7⟩ .write
                      |>.insertOrMerge ⟨.tcb, ObjId.ofNat 3⟩ .write
                      |>.insertOrMerge ⟨.tcb, ObjId.ofNat 5⟩ .write
  let withinKindExpected : List (LockId × AccessMode) :=
    [(⟨.tcb, ObjId.ofNat 3⟩, .write),
     (⟨.tcb, ObjId.ofNat 5⟩, .write),
     (⟨.tcb, ObjId.ofNat 7⟩, .write)]
  assertBool "lockAcquireSequence: within-kind sort by ObjId ascending"
    (decide (withinKind.lockAcquireSequence = withinKindExpected))

private def runLockKindCoDomainChecks : IO Unit := do
  IO.println "--- §14 lockKind co-domain (audit-pass-2) ---"
  -- Audit-pass-2: substantive co-domain claim — lockKind returns one
  -- of the 7 modeled kinds, never .objStore / .reply / .page.
  let ep : KernelObject := KernelObject.endpoint ({} : Endpoint)
  let u : KernelObject := KernelObject.untyped
    { regionBase := PAddr.ofNat 0, regionSize := 4096 }
  assertBool "endpoint.lockKind ≠ .objStore"
    (decide (ep.lockKind ≠ .objStore))
  assertBool "endpoint.lockKind ≠ .reply"
    (decide (ep.lockKind ≠ .reply))
  assertBool "endpoint.lockKind ≠ .page"
    (decide (ep.lockKind ≠ .page))
  assertBool "untyped.lockKind ≠ .objStore"
    (decide (u.lockKind ≠ .objStore))
  assertBool "untyped.lockKind ≠ .reply"
    (decide (u.lockKind ≠ .reply))
  assertBool "untyped.lockKind ≠ .page"
    (decide (u.lockKind ≠ .page))
  assertBool "endpoint.lockKind is one of the 7 modeled kinds"
    (decide (ep.lockKind = .tcb ∨ ep.lockKind = .endpoint ∨
             ep.lockKind = .notification ∨ ep.lockKind = .cnode ∨
             ep.lockKind = .vspaceRoot ∨ ep.lockKind = .untyped ∨
             ep.lockKind = .schedContext))
  -- The new substantive theorems are surface-anchored via #check
  -- above; their content is exercised by the decidable assertions
  -- preceding this line (e.g. "endpoint.lockKind is one of the 7
  -- modeled kinds" applies the same Or-chain via decide).

private def runFstInjChecks : IO Unit := do
  IO.println "--- §15 LockSet.fst_inj_at_pairs (audit-pass-2) ---"
  -- Construct a 2-element LockSet and verify membership.  The
  -- `fst_inj_at_pairs` theorem itself is exercised via the
  -- `canonical-sort` proof internally (uniqueness uses it); a
  -- self-application "(p, p) ↦ p = p" is trivial.  We instead
  -- exercise the contrapositive: two distinct pairs in a LockSet
  -- have distinct `fst` keys (since equal-fst would collapse them
  -- via insertOrMerge).
  let p1 : LockId × AccessMode := (⟨.tcb, ObjId.ofNat 1⟩, .write)
  let p2 : LockId × AccessMode := (⟨.endpoint, ObjId.ofNat 2⟩, .write)
  let S := (LockSet.singleton p1.fst p1.snd).union (LockSet.singleton p2.fst p2.snd)
  assertBool "S contains p1"
    (decide (p1 ∈ S.pairs))
  assertBool "S contains p2"
    (decide (p2 ∈ S.pairs))
  -- The projected keys list is Nodup (the structural invariant).
  assertBool "S.hUniqueKeys (projected keys are Nodup)"
    (decide ((S.pairs.map (·.fst)).Nodup))
  -- Two distinct pairs must have distinct fst (contrapositive of fst_inj).
  assertBool "p1.fst ≠ p2.fst"
    (decide (p1.fst ≠ p2.fst))

private def runLookupFixtureChecks : IO Unit := do
  IO.println "--- §13 LockId.lookup on non-default fixture state ---"
  let ep : KernelObject := KernelObject.endpoint ({} : Endpoint)
  let s : SystemState := {
    (default : SystemState) with
      objects := (default : SystemState).objects.insert (ObjId.ofNat 5) ep
  }
  -- Right kind, right ObjId → some.
  assertBool "LockId.lookup at (.endpoint, 5) on state-with-endpoint: some"
    (LockId.lookup s ⟨.endpoint, ObjId.ofNat 5⟩).isSome
  -- Wrong kind (TCB at Endpoint's ObjId) → none.
  assertBool "LockId.lookup at (.tcb, 5) on state-with-endpoint: none (kind mismatch)"
    (decide (LockId.lookup s ⟨.tcb, ObjId.ofNat 5⟩ = none))
  assertBool "LockId.lookup at (.cnode, 5) on state-with-endpoint: none (kind mismatch)"
    (decide (LockId.lookup s ⟨.cnode, ObjId.ofNat 5⟩ = none))
  -- Right kind, wrong ObjId → none.
  assertBool "LockId.lookup at (.endpoint, 99) on state-with-endpoint: none (absent ObjId)"
    (decide (LockId.lookup s ⟨.endpoint, ObjId.ofNat 99⟩ = none))
  -- Fail-closed for N/A kinds.
  assertBool "LockId.lookup at (.objStore, 0): none (no object for table-level lock)"
    (decide (LockId.lookup s ⟨.objStore, ObjId.ofNat 0⟩ = none))
  assertBool "LockId.lookup at (.reply, 0): none (SM3.A.5 N/A)"
    (decide (LockId.lookup s ⟨.reply, ObjId.ofNat 0⟩ = none))
  assertBool "LockId.lookup at (.page, 0): none (SM3.A.8 N/A)"
    (decide (LockId.lookup s ⟨.page, ObjId.ofNat 0⟩ = none))

private def runInventoryChecks : IO Unit := do
  IO.println "--- §8 Inventory aggregator ---"
  assertBool "lockSetTheorems.length = 113"
    (decide (lockSetTheorems.length = 113))
  assertBool "projection category count = 22"
    (decide ((lockSetTheorems.filter (fun t => t.category == .projection)).length = 22))
  assertBool "lockSet category count = 35 (one per SyscallId variant)"
    (decide ((lockSetTheorems.filter (fun t => t.category == .lockSet)).length = 35))
  assertBool "consistency category count = 35 (one per SyscallId variant)"
    (decide ((lockSetTheorems.filter (fun t => t.category == .consistency)).length = 35))
  assertBool "acquireSort category count = 6"
    (decide ((lockSetTheorems.filter (fun t => t.category == .acquireSort)).length = 6))
  assertBool "algebra category count = 9"
    (decide ((lockSetTheorems.filter (fun t => t.category == .algebra)).length = 9))
  assertBool "chainStart category count = 6 (audit-pass-5 markers + SM6.E suspend + WS-OD OD3.14's two)"
    (decide ((lockSetTheorems.filter (fun t => t.category == .chainStart)).length = 6))
  assertBool "category-partition sum = total"
    (decide
      ((lockSetTheorems.filter (fun t => t.category == .projection)).length +
       (lockSetTheorems.filter (fun t => t.category == .lockSet)).length +
       (lockSetTheorems.filter (fun t => t.category == .consistency)).length +
       (lockSetTheorems.filter (fun t => t.category == .acquireSort)).length +
       (lockSetTheorems.filter (fun t => t.category == .algebra)).length +
       (lockSetTheorems.filter (fun t => t.category == .chainStart)).length =
       lockSetTheorems.length))

private def runPipChainStartChecks : IO Unit := do
  IO.println "--- §16 PIP chain-walk start markers (audit-pass-5) ---"
  -- pipChainStart_endpointCall mirrors receiverTid exactly.
  assertBool "pipChainStart_endpointCall: receiverTid = none ⇒ chain-start = none"
    (decide (pipChainStart_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
              none none = none))
  assertBool "pipChainStart_endpointCall: receiverTid = some ⟨8⟩ ⇒ chain-start = some ⟨8⟩"
    (decide (pipChainStart_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
              (some ⟨8⟩) none = some ⟨8⟩))
  assertBool "pipChainStart_endpointCall: donation arg does not affect chain-start"
    (decide (pipChainStart_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
              (some ⟨8⟩) (some ⟨100⟩) = some ⟨8⟩))
  -- pipChainStart_endpointReply always emits revertPIP at the caller (= replier).
  assertBool "pipChainStart_endpointReply: always = some callerTid"
    (decide (pipChainStart_endpointReply ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩
              none none = some ⟨5⟩))
  assertBool "pipChainStart_endpointReply: donation args do not affect chain-start"
    (decide (pipChainStart_endpointReply ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩
              (some ⟨42⟩) (some ⟨7⟩) = some ⟨5⟩))
  -- pipChainStart_replyRecv names the RECORDED SERVER (WS-OD OD3.14): the reply
  -- leg walks from the thread whose waiter set it shrank, which is the receiver
  -- only when the reply capability was not delegated.
  assertBool "pipChainStart_replyRecv: non-delegated ⇒ the receiver"
    (decide (pipChainStart_replyRecv ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩ (ObjId.ofNat 20)
              none none none ⟨5⟩ = some ⟨5⟩))
  assertBool "pipChainStart_replyRecv: DELEGATED ⇒ the recorded server, not the receiver"
    (decide (pipChainStart_replyRecv ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩ (ObjId.ofNat 20)
              (some ⟨11⟩) (some ⟨42⟩) (some ⟨7⟩) ⟨9⟩ = some ⟨9⟩))
  -- WS-OD OD3.14: `.replyRecv`'s SECOND walk, and `.receive`'s new one.
  assertBool "pipChainStart_replyRecvReceiveLeg: non-delegated ⇒ none (the reply leg covered it)"
    (decide (pipChainStart_replyRecvReceiveLeg ⟨5⟩ ⟨5⟩ (some ⟨11⟩) = none))
  assertBool "pipChainStart_replyRecvReceiveLeg: delegated but no Call dequeued ⇒ none"
    (decide (pipChainStart_replyRecvReceiveLeg ⟨5⟩ ⟨9⟩ none = none))
  assertBool "pipChainStart_replyRecvReceiveLeg: delegated with a dequeued Call ⇒ the receiver"
    (decide (pipChainStart_replyRecvReceiveLeg ⟨5⟩ ⟨9⟩ (some ⟨11⟩) = some ⟨5⟩))
  assertBool "pipChainStart_endpointReceive: no Call dequeued ⇒ none"
    (decide (pipChainStart_endpointReceive ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
              none = none))
  assertBool "pipChainStart_endpointReceive: a dequeued Call ⇒ the receiver"
    (decide (pipChainStart_endpointReceive ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
              (some ⟨11⟩) = some ⟨5⟩))
  -- Defense-in-depth: the chain-start TCB equals the receiver in `.call`
  -- handshake mode, so the static lockSet (which includes receiverTid in
  -- its `tcbLock receiverTid .write` entry) already covers the chain
  -- entry point.  SM3.C's dynamic walker then extends past startTid.
  assertBool "pipChainStart_endpointCall: chain-start is contained in static lockSet"
    (let st := pipChainStart_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
                 (some ⟨8⟩) none
     let ls := lockSet_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
                 (some ⟨8⟩) none
     match st with
     | none => true
     | some tid => decide (ls.containsKey ⟨.tcb, ObjId.ofNat tid.toNat⟩ = true))
  assertBool "pipChainStart_endpointReply: chain-start callerTid is in static lockSet"
    (let st := pipChainStart_endpointReply ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩
                 none none
     let ls := lockSet_endpointReply ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩
                 none none none none none
     match st with
     | none => true
     | some tid => decide (ls.containsKey ⟨.tcb, ObjId.ofNat tid.toNat⟩ = true))

def runLockSetChecks : IO Unit := do
  IO.println "WS-SM SM3.B — LockSet regression suite"
  IO.println "======================================"
  runLockSetCoreChecks
  runLockSetAcquireSortChecks
  runAccessModeAlgebraChecks
  runPermittedKindsChecks
  runLockKindHelpersChecks
  runLockIdProjectionChecks
  runPerTransitionShapeChecks
  runInventoryChecks
  runLubMergeChecks
  runUnionChecks
  runConsistencyRuntimeChecks
  runCanonicalSortRuntimeChecks
  runLookupFixtureChecks
  runLockKindCoDomainChecks
  runFstInjChecks
  runPipChainStartChecks
  runAuditPass6FootprintChecks
  runQueueOwnerFootprintChecks
  runDonationPushFootprintChecks
  IO.println "======================================"
  IO.println "All SM3.B LockSet checks PASS."

end SeLe4n.Testing.LockSet

def main : IO Unit :=
  SeLe4n.Testing.LockSet.runLockSetChecks
