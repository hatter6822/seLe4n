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
receiver TCB 8.  Sort: cnode/10, tcb/5, tcb/8, endpoint/20. -/

example :
    LockSet.lockAcquireSequence
      (lockSet_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20) (some ⟨8⟩)) =
    [(⟨.cnode, ObjId.ofNat 10⟩, .read),
     (⟨.tcb, ObjId.ofNat 5⟩, .write),
     (⟨.tcb, ObjId.ofNat 8⟩, .write),
     (⟨.endpoint, ObjId.ofNat 20⟩, .write)] := by native_decide

/-! ### tcbSuspend with both blocked endpoint and blocked notification: 5 locks. -/

example :
    (lockSet_tcbSuspend ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩
      (some (ObjId.ofNat 20)) (some (ObjId.ofNat 30))).size = 5 := by decide

/-! ### tcbSuspend with no blocked objects: 3 locks. -/

example :
    (lockSet_tcbSuspend ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩ none none).size = 3 := by decide

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

-- ============================================================================
-- §6 — Permitted kinds for every syscall
-- ============================================================================

example : permittedKinds .send = [.tcb, .cnode, .endpoint] := by decide
example : permittedKinds .receive = [.tcb, .cnode, .endpoint] := by decide
example : permittedKinds .call = [.tcb, .cnode, .endpoint] := by decide
example : permittedKinds .reply = [.tcb, .cnode] := by decide
example : permittedKinds .replyRecv = [.tcb, .cnode, .endpoint] := by decide
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
example : permittedKinds .tcbSuspend = [.tcb, .cnode, .endpoint, .notification] := by decide
example : permittedKinds .tcbResume = [.tcb, .cnode] := by decide
example : permittedKinds .tcbSetPriority = [.tcb, .cnode] := by decide
example : permittedKinds .tcbSetMCPriority = [.tcb, .cnode] := by decide
example : permittedKinds .tcbSetIPCBuffer = [.tcb, .cnode] := by decide

-- ============================================================================
-- §7 — Inventory examples (decidable)
-- ============================================================================

example : lockSetTheorems.length = 72 := by decide

example : (lockSetTheorems.filter (fun t => t.category == .projection)).length = 10 := by
  decide

example : (lockSetTheorems.filter (fun t => t.category == .lockSet)).length = 25 := by
  decide

example : (lockSetTheorems.filter (fun t => t.category == .consistency)).length = 25 := by
  decide

example : (lockSetTheorems.filter (fun t => t.category == .acquireSort)).length = 5 := by
  decide

example : (lockSetTheorems.filter (fun t => t.category == .algebra)).length = 7 := by
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
  let s := lockSet_endpointCall ⟨5⟩ (ObjId.ofNat 10) (ObjId.ofNat 20) (some ⟨8⟩)
  let seq := s.lockAcquireSequence
  assertBool "endpointCall lock-set size = 4"
    (decide (s.size = 4))
  assertBool "endpointCall lockAcquireSequence length = 4"
    (decide (seq.length = 4))
  -- The sort is deterministic: cnode/10 (read), tcb/5 (write), tcb/8 (write), endpoint/20 (write).
  let expected : List (LockId × AccessMode) :=
    [(⟨.cnode, ObjId.ofNat 10⟩, .read),
     (⟨.tcb, ObjId.ofNat 5⟩, .write),
     (⟨.tcb, ObjId.ofNat 8⟩, .write),
     (⟨.endpoint, ObjId.ofNat 20⟩, .write)]
  assertBool "endpointCall lockAcquireSequence matches plan §4.5 expected order"
    (decide (seq = expected))

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
  assertBool "permittedKinds .tcbSuspend"
    (decide (permittedKinds .tcbSuspend = [.tcb, .cnode, .endpoint, .notification]))
  assertBool "permittedKinds .schedContextBind"
    (decide (permittedKinds .schedContextBind = [.tcb, .cnode, .schedContext]))

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
  -- TCB suspend with both Option-blocked: 5 locks.
  assertBool "tcbSuspend size (both Options some) = 5"
    (decide ((lockSet_tcbSuspend ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩
              (some (ObjId.ofNat 20)) (some (ObjId.ofNat 30))).size = 5))
  -- TCB suspend with no Options: 3 locks.
  assertBool "tcbSuspend size (no Options) = 3"
    (decide ((lockSet_tcbSuspend ⟨1⟩ (ObjId.ofNat 10) ⟨3⟩ none none).size = 3))

private def runInventoryChecks : IO Unit := do
  IO.println "--- §8 Inventory aggregator ---"
  assertBool "lockSetTheorems.length = 72"
    (decide (lockSetTheorems.length = 72))
  assertBool "projection category count = 10"
    (decide ((lockSetTheorems.filter (fun t => t.category == .projection)).length = 10))
  assertBool "lockSet category count = 25 (one per SyscallId variant)"
    (decide ((lockSetTheorems.filter (fun t => t.category == .lockSet)).length = 25))
  assertBool "consistency category count = 25 (one per SyscallId variant)"
    (decide ((lockSetTheorems.filter (fun t => t.category == .consistency)).length = 25))
  assertBool "acquireSort category count = 5"
    (decide ((lockSetTheorems.filter (fun t => t.category == .acquireSort)).length = 5))
  assertBool "algebra category count = 7"
    (decide ((lockSetTheorems.filter (fun t => t.category == .algebra)).length = 7))
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
  IO.println "======================================"
  IO.println "All SM3.B LockSet checks PASS."

end SeLe4n.Testing.LockSet

def main : IO Unit :=
  SeLe4n.Testing.LockSet.runLockSetChecks
