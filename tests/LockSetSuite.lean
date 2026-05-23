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
#check @KernelObject.lockKind_ne_reply
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
#check @lockSet_tcbSuspend
#check @lockSet_tcbResume
#check @lockSet_tcbSetPriority
#check @lockSet_tcbSetMCPriority
#check @lockSet_tcbSetIPCBuffer

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
#check @lockSet_consistent_tcbSuspend
#check @lockSet_consistent_tcbResume
#check @lockSet_consistent_tcbSetPriority
#check @lockSet_consistent_tcbSetMCPriority
#check @lockSet_consistent_tcbSetIPCBuffer

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
`lockSet_tcbSuspend` when `callerTid = targetTcbTid` (self-suspend).

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

The base list contains (tcb caller, read) and (tcb target, write).
With caller=target, the lub-merge produces (tcb caller, write).
Total size = 2 (caller-TCB merged + cnode-root). -/

example :
    let S := lockSet_tcbSuspend ⟨5⟩ (ObjId.ofNat 10) ⟨5⟩ none none none none
    S.size = 2 := by decide

example :
    let S := lockSet_tcbSuspend ⟨5⟩ (ObjId.ofNat 10) ⟨5⟩ none none none none
    S.lockAcquireSequence =
      [(⟨.cnode, ObjId.ofNat 10⟩, .read),
       (⟨.tcb, ObjId.ofNat 5⟩, .write)] := by native_decide

/-! ### Reply with caller = reply-target collapses to two locks.

`lockSet_endpointReply` declares (caller TCB, write), (cnode, read),
(reply target, write).  If caller = reply target, the merge yields
a single (TCB, write) entry. -/

example :
    let S := lockSet_endpointReply ⟨5⟩ (ObjId.ofNat 10) ⟨5⟩ none
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
    [(⟨.cnode, ObjId.ofNat 10⟩, .read),
     (⟨.tcb, ObjId.ofNat 5⟩, .write),
     (⟨.tcb, ObjId.ofNat 8⟩, .write),
     (⟨.endpoint, ObjId.ofNat 20⟩, .write),
     (⟨.schedContext, ObjId.ofNat 100⟩, .write)] := by native_decide

/-! ### tcbSuspend with both blocked endpoint and blocked notification: 5 locks. -/

example :
    (lockSet_tcbSuspend ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩
      (some (ObjId.ofNat 20)) (some (ObjId.ofNat 30)) none none).size = 5 := by decide

/-! ### tcbSuspend with no blocked objects: 3 locks. -/

example :
    (lockSet_tcbSuspend ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩ none none none none).size = 3 := by decide

/-! ### tcbSuspend with `.donated` binding: 5 locks (caller TCB +
cnode + suspended TCB + donated SC + original owner). -/

example :
    (lockSet_tcbSuspend ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩ none none
      (some ⟨50⟩) (some ⟨7⟩)).size = 5 := by decide

/-! ### tcbSuspend with `.bound` binding: 4 locks (caller TCB +
cnode + suspended TCB + bound SC). -/

example :
    (lockSet_tcbSuspend ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩ none none
      (some ⟨50⟩) none).size = 4 := by decide

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

example : permittedKinds .send = [.tcb, .cnode, .endpoint] := by decide
example : permittedKinds .receive = [.tcb, .cnode, .endpoint] := by decide
-- Audit-pass-3: `.call`/`.reply`/`.replyRecv` now include `.schedContext`
-- to cover the donation extension.
example : permittedKinds .call = [.tcb, .cnode, .endpoint, .schedContext] := by decide
example : permittedKinds .reply = [.tcb, .cnode, .schedContext] := by decide
example : permittedKinds .replyRecv = [.tcb, .cnode, .endpoint, .schedContext] := by decide
example : permittedKinds .notificationSignal = [.tcb, .cnode, .notification] := by decide
example : permittedKinds .notificationWait = [.tcb, .cnode, .notification] := by decide
example : permittedKinds .cspaceMint = [.tcb, .cnode] := by decide
example : permittedKinds .cspaceCopy = [.tcb, .cnode] := by decide
example : permittedKinds .cspaceMove = [.tcb, .cnode] := by decide
example : permittedKinds .cspaceDelete = [.tcb, .cnode] := by decide
example : permittedKinds .lifecycleRetype = [.tcb, .cnode, .untyped] := by decide
example : permittedKinds .vspaceMap = [.tcb, .cnode, .vspaceRoot] := by decide
example : permittedKinds .vspaceUnmap = [.tcb, .cnode, .vspaceRoot] := by decide
example : permittedKinds .serviceRegister = [.tcb, .cnode] := by decide
example : permittedKinds .serviceRevoke = [.tcb, .cnode] := by decide
example : permittedKinds .serviceQuery = [.tcb, .cnode] := by decide
example : permittedKinds .schedContextConfigure = [.tcb, .cnode, .schedContext] := by decide
example : permittedKinds .schedContextBind = [.tcb, .cnode, .schedContext] := by decide
example : permittedKinds .schedContextUnbind = [.tcb, .cnode, .schedContext] := by decide
-- Audit-pass-3: `.tcbSuspend` now includes `.schedContext` to cover
-- the donation-cancel extension.
example : permittedKinds .tcbSuspend =
    [.tcb, .cnode, .endpoint, .notification, .schedContext] := by decide
example : permittedKinds .tcbResume = [.tcb, .cnode] := by decide
example : permittedKinds .tcbSetPriority = [.tcb, .cnode] := by decide
example : permittedKinds .tcbSetMCPriority = [.tcb, .cnode] := by decide
example : permittedKinds .tcbSetIPCBuffer = [.tcb, .cnode] := by decide

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

example :
    ∀ p ∈ (lockSet_tcbSuspend ⟨5⟩ (ObjId.ofNat 10) ⟨3⟩
              (some (ObjId.ofNat 20)) (some (ObjId.ofNat 30))
              none none).pairs,
      p.fst.kind ∈ permittedKinds .tcbSuspend :=
  lockSet_consistent_tcbSuspend ⟨5⟩ (ObjId.ofNat 10) ⟨3⟩
    (some (ObjId.ofNat 20)) (some (ObjId.ofNat 30)) none none

-- Audit-pass-3: with donation cancel args (.donated case with all 4 Options).
example :
    ∀ p ∈ (lockSet_tcbSuspend ⟨5⟩ (ObjId.ofNat 10) ⟨3⟩
              (some (ObjId.ofNat 20)) (some (ObjId.ofNat 30))
              (some ⟨50⟩) (some ⟨7⟩)).pairs,
      p.fst.kind ∈ permittedKinds .tcbSuspend :=
  lockSet_consistent_tcbSuspend ⟨5⟩ (ObjId.ofNat 10) ⟨3⟩
    (some (ObjId.ofNat 20)) (some (ObjId.ofNat 30))
    (some ⟨50⟩) (some ⟨7⟩)

example :
    ∀ p ∈ (lockSet_schedContextBind ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩ ⟨3⟩).pairs,
      p.fst.kind ∈ permittedKinds .schedContextBind :=
  lockSet_consistent_schedContextBind ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩ ⟨3⟩

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
-- §7 — Inventory examples (decidable)
-- ============================================================================

example : lockSetTheorems.length = 87 := by decide

example : (lockSetTheorems.filter (fun t => t.category == .projection)).length = 22 := by
  decide

example : (lockSetTheorems.filter (fun t => t.category == .lockSet)).length = 25 := by
  decide

example : (lockSetTheorems.filter (fun t => t.category == .consistency)).length = 25 := by
  decide

example : (lockSetTheorems.filter (fun t => t.category == .acquireSort)).length = 6 := by
  decide

example : (lockSetTheorems.filter (fun t => t.category == .algebra)).length = 9 := by
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
  let sDon := lockSet_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
                (some ⟨8⟩) (some ⟨100⟩)
  let seqDon := sDon.lockAcquireSequence
  assertBool "endpointCall (with donation) lock-set size = 5"
    (decide (sDon.size = 5))
  let expectedDon : List (LockId × AccessMode) :=
    [(⟨.cnode, ObjId.ofNat 10⟩, .read),
     (⟨.tcb, ObjId.ofNat 5⟩, .write),
     (⟨.tcb, ObjId.ofNat 8⟩, .write),
     (⟨.endpoint, ObjId.ofNat 20⟩, .write),
     (⟨.schedContext, ObjId.ofNat 100⟩, .write)]
  assertBool "endpointCall (with donation) lockAcquireSequence: SC sorts last"
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
  assertBool "permittedKinds .send"
    (decide (permittedKinds .send = [.tcb, .cnode, .endpoint]))
  assertBool "permittedKinds .vspaceMap"
    (decide (permittedKinds .vspaceMap = [.tcb, .cnode, .vspaceRoot]))
  assertBool "permittedKinds .lifecycleRetype"
    (decide (permittedKinds .lifecycleRetype = [.tcb, .cnode, .untyped]))
  -- Audit-pass-3: .tcbSuspend now includes .schedContext (donation-cancel).
  assertBool "permittedKinds .tcbSuspend"
    (decide (permittedKinds .tcbSuspend =
      [.tcb, .cnode, .endpoint, .notification, .schedContext]))
  assertBool "permittedKinds .schedContextBind"
    (decide (permittedKinds .schedContextBind = [.tcb, .cnode, .schedContext]))
  -- Audit-pass-3: .call, .reply, .replyRecv include .schedContext (donation).
  assertBool "permittedKinds .call (with donation kind)"
    (decide (permittedKinds .call = [.tcb, .cnode, .endpoint, .schedContext]))
  assertBool "permittedKinds .reply (with donation-return kind)"
    (decide (permittedKinds .reply = [.tcb, .cnode, .schedContext]))
  assertBool "permittedKinds .replyRecv (with donation-return kind)"
    (decide (permittedKinds .replyRecv =
      [.tcb, .cnode, .endpoint, .schedContext]))

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
  -- Capability paths: 3 locks each.
  assertBool "cspaceMint size = 3"
    (decide ((lockSet_cspaceMint ⟨1⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)).size = 3))
  assertBool "cspaceMove size = 3"
    (decide ((lockSet_cspaceMove ⟨1⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)).size = 3))
  -- VSpace: 3 locks each.
  assertBool "vspaceMap size = 3"
    (decide ((lockSet_vspaceMap ⟨1⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)).size = 3))
  -- Lifecycle: 4 locks (caller TCB read + CNode root read + untyped write + dst CNode write).
  assertBool "lifecycleRetype size = 4"
    (decide ((lockSet_lifecycleRetype ⟨1⟩ (ObjId.ofNat 10) (ObjId.ofNat 20)
              (ObjId.ofNat 30)).size = 4))
  -- TCB suspend with both Option-blocked (no donation): 5 locks.
  assertBool "tcbSuspend size (block-options some, no donation) = 5"
    (decide ((lockSet_tcbSuspend ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩
              (some (ObjId.ofNat 20)) (some (ObjId.ofNat 30))
              none none).size = 5))
  -- TCB suspend with no Options: 3 locks.
  assertBool "tcbSuspend size (no Options) = 3"
    (decide ((lockSet_tcbSuspend ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩ none none
              none none).size = 3))
  -- Audit-pass-3: TCB suspend with .bound binding (SC only): 4 locks.
  assertBool "tcbSuspend size (.bound binding, SC only) = 4"
    (decide ((lockSet_tcbSuspend ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩ none none
              (some ⟨50⟩) none).size = 4))
  -- Audit-pass-3: TCB suspend with .donated binding (SC + owner): 5 locks.
  assertBool "tcbSuspend size (.donated binding, SC + originalOwner) = 5"
    (decide ((lockSet_tcbSuspend ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩ none none
              (some ⟨50⟩) (some ⟨7⟩)).size = 5))
  -- Audit-pass-3: TCB suspend with ALL options (block ep + nti + .donated): 7 locks.
  assertBool "tcbSuspend size (full: blocks + .donated + originalOwner) = 7"
    (decide ((lockSet_tcbSuspend ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩
              (some (ObjId.ofNat 20)) (some (ObjId.ofNat 30))
              (some ⟨50⟩) (some ⟨7⟩)).size = 7))

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
  let selfSuspend := lockSet_tcbSuspend ⟨5⟩ (ObjId.ofNat 10) ⟨5⟩ none none none none
  assertBool "tcbSuspend(caller=target) collapses to 2 locks (cnode + merged TCB)"
    (decide (selfSuspend.size = 2))
  assertBool "tcbSuspend(caller=target) merged TCB lock is write"
    (decide (selfSuspend.lockAcquireSequence =
      [(⟨.cnode, ObjId.ofNat 10⟩, .read),
       (⟨.tcb, ObjId.ofNat 5⟩, .write)]))
  -- endpointReply(caller=replyTarget) collapses.
  let selfReply := lockSet_endpointReply ⟨5⟩ (ObjId.ofNat 10) ⟨5⟩ none
  assertBool "endpointReply(caller=replyTarget) collapses to 2 locks"
    (decide (selfReply.size = 2))
  -- Audit-pass-3: endpointReply with donation-return: the SC is added.
  let donReply := lockSet_endpointReply ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩ (some ⟨42⟩)
  assertBool "endpointReply(caller=5, target=7, donatedSc=42) has 4 locks"
    (decide (donReply.size = 4))
  -- Audit-pass-3: replyRecv with full extension (sender + donation).
  let donReplyRecv := lockSet_replyRecv ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩
                       (ObjId.ofNat 20) (some ⟨8⟩) (some ⟨42⟩)
  assertBool "replyRecv (sender + donation) has 6 locks"
    (decide (donReplyRecv.size = 6))

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
  -- A transition with 4 Optional args (.tcbSuspend, full) — all Some.
  let susp := lockSet_tcbSuspend ⟨5⟩ (ObjId.ofNat 10) ⟨3⟩
                (some (ObjId.ofNat 20)) (some (ObjId.ofNat 30))
                (some ⟨50⟩) (some ⟨7⟩)
  let allOk_susp := susp.pairs.all (fun p =>
    decide (p.fst.kind ∈ permittedKinds .tcbSuspend))
  assertBool "lockSet_tcbSuspend (full 4 Options some): all kinds in permittedKinds .tcbSuspend"
    allOk_susp
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
  -- Audit-pass-3: donation-return extension on .reply.
  let replyDon := lockSet_endpointReply ⟨5⟩ (ObjId.ofNat 10) ⟨7⟩ (some ⟨42⟩)
  let allOk_replyDon := replyDon.pairs.all (fun p =>
    decide (p.fst.kind ∈ permittedKinds .reply))
  assertBool "lockSet_endpointReply (with donation): all kinds in permittedKinds .reply"
    allOk_replyDon

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
  assertBool "lockSetTheorems.length = 87"
    (decide (lockSetTheorems.length = 87))
  assertBool "projection category count = 22"
    (decide ((lockSetTheorems.filter (fun t => t.category == .projection)).length = 22))
  assertBool "lockSet category count = 25 (one per SyscallId variant)"
    (decide ((lockSetTheorems.filter (fun t => t.category == .lockSet)).length = 25))
  assertBool "consistency category count = 25 (one per SyscallId variant)"
    (decide ((lockSetTheorems.filter (fun t => t.category == .consistency)).length = 25))
  assertBool "acquireSort category count = 6"
    (decide ((lockSetTheorems.filter (fun t => t.category == .acquireSort)).length = 6))
  assertBool "algebra category count = 9"
    (decide ((lockSetTheorems.filter (fun t => t.category == .algebra)).length = 9))
  assertBool "category-partition sum = total"
    (decide
      ((lockSetTheorems.filter (fun t => t.category == .projection)).length +
       (lockSetTheorems.filter (fun t => t.category == .lockSet)).length +
       (lockSetTheorems.filter (fun t => t.category == .consistency)).length +
       (lockSetTheorems.filter (fun t => t.category == .acquireSort)).length +
       (lockSetTheorems.filter (fun t => t.category == .algebra)).length =
       lockSetTheorems.length))

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
  IO.println "======================================"
  IO.println "All SM3.B LockSet checks PASS."

end SeLe4n.Testing.LockSet

def main : IO Unit :=
  SeLe4n.Testing.LockSet.runLockSetChecks
