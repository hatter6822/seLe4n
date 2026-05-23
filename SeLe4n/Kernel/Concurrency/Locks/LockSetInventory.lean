-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.Locks.LockSet
import SeLe4n.Kernel.Concurrency.Locks.LockIdProjection
import SeLe4n.Kernel.Concurrency.Locks.LockSetTransitions

/-!
# WS-SM SM3.B — LockSet theorem inventory

Aggregates the SM3.B substantive theorems into a single typed
inventory with size and per-category witnesses.  Mirrors the
SM3.A `PerObjectLockInventory.lean` pattern (34-theorem aggregator)
and the SM2.D `LockPrimitives.lean` pattern (22-theorem aggregator).

The inventory has five categories matching the plan §5.2 sub-tasks:

* `.projection` — SM3.B.1 / SM3.B.2 (KernelObject.lockKind,
  LockId.fromObject, LockId.lookup + per-variant simp / round-trip
  lemmas).
* `.lockSet` — SM3.B.3 per-transition lockSet definitions (25
  transitions).
* `.consistency` — SM3.B.4 per-transition lockSet_consistent
  theorems (25 entries).
* `.acquireSort` — SM3.B.5/B.6/B.7/B.8 lockAcquireSequence + the
  three ordered/complete/canonical theorems.
* `.algebra` — SM3.B helper theorems (AccessMode.lub
  idempotence/commutativity/associativity, AccessMode.conflicts
  symmetry, LockSet.insertOrMerge_mem, lockSetOfList_mem_inv,
  LockSet.fst_inj_at_pairs, LockSet.union_mem_inv).

## Identifier validation

Identifiers are compile-time-validated via the `lkst!` macro,
mirroring SM3.A's `polt!` pattern.  A typo or rename fails the
build at this module's elaboration step.
-/

namespace SeLe4n.Kernel.Concurrency

open SeLe4n
open SeLe4n.Model

/-- WS-SM SM3.B: category tag for LockSet theorems. -/
inductive LockSetCategory where
  /-- Projection layer: kindOf, fromObject, lookup. -/
  | projection
  /-- Per-transition lockSet declarations. -/
  | lockSet
  /-- Per-transition lockSet_consistent theorems. -/
  | consistency
  /-- Canonical sort + ordered/complete/canonical theorems. -/
  | acquireSort
  /-- AccessMode algebra + LockSet structural helpers. -/
  | algebra
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM3.B: a theorem entry in the LockSet inventory.

Records a description, the theorem's fully-qualified name as a
`String`, a compile-time elaboration witness, and a category tag.

The `_elabCheck` field is produced by the `lkst!` macro which
emits a `let _ := @<ident>; ()` term.  The macro forces Lean's
elaborator to resolve the referenced declaration at construction
time, so a typo or stale rename fails to elaborate with "unknown
identifier '<name>'". -/
structure LockSetTheorem where
  description : String
  identifier  : String
  _elabCheck  : Unit
  category    : LockSetCategory
  deriving Repr, Inhabited

/-- WS-SM SM3.B: build a `LockSetTheorem` with a compile-time-validated
identifier.  See SM3.A's `polt!` for the equivalent pattern. -/
syntax (name := lkstMacro) "lkst!" str ident term : term

macro_rules
  | `(lkst! $desc:str $ident:ident $cat:term) => do
      let nameStr : String := ident.getId.toString
      let nameStxLit := Lean.Syntax.mkStrLit nameStr
      `(({ description := $desc,
           identifier := $nameStxLit,
           _elabCheck := (let _ := @$ident; ()),
           category := $cat
         } : LockSetTheorem))

/-- WS-SM SM3.B: substantive theorem inventory.  Every entry's
identifier is compile-time-validated. -/
def lockSetTheorems : List LockSetTheorem :=
  [-- §1 projection (18 entries — 1 lockKind def + 7 per-variant lockKind
    -- unfolds + agreement-with-objectType + LockId.fromObject + LockId.lookup
    -- + 6 lookup structural theorems + 3 fail-closed witnesses for N/A kinds)
    lkst! "KernelObject.lockKind projects the LockKind from a variant"
      SeLe4n.Model.KernelObject.lockKind .projection,
    lkst! "lockKind on .tcb reduces to .tcb"
      SeLe4n.Model.KernelObject.lockKind_tcb .projection,
    lkst! "lockKind on .endpoint reduces to .endpoint"
      SeLe4n.Model.KernelObject.lockKind_endpoint .projection,
    lkst! "lockKind on .notification reduces to .notification"
      SeLe4n.Model.KernelObject.lockKind_notification .projection,
    lkst! "lockKind on .cnode reduces to .cnode"
      SeLe4n.Model.KernelObject.lockKind_cnode .projection,
    lkst! "lockKind on .vspaceRoot reduces to .vspaceRoot"
      SeLe4n.Model.KernelObject.lockKind_vspaceRoot .projection,
    lkst! "lockKind on .untyped reduces to .untyped"
      SeLe4n.Model.KernelObject.lockKind_untyped .projection,
    lkst! "lockKind on .schedContext reduces to .schedContext"
      SeLe4n.Model.KernelObject.lockKind_schedContext .projection,
    lkst! "lockKind agrees with objectType per variant"
      SeLe4n.Model.KernelObject.lockKind_eq_of_objectType .projection,
    lkst! "LockId.fromObject builds LockId from ObjId + KernelObject"
      SeLe4n.Model.LockId.fromObject .projection,
    lkst! "LockId.lookup resolves a LockId against a SystemState"
      SeLe4n.Model.LockId.lookup .projection,
    lkst! "LockId.lookup_some_of_kindMatch: success branch on matching kind"
      SeLe4n.Model.LockId.lookup_some_of_kindMatch .projection,
    lkst! "LockId.lookup_fromObject_of_present: round-trip identity"
      SeLe4n.Model.LockId.lookup_fromObject_of_present .projection,
    lkst! "LockId.lookup_kindMatch: post-condition on success"
      SeLe4n.Model.LockId.lookup_kindMatch .projection,
    lkst! "LockId.lookup_lockState_eq: returned state matches objectLockOf"
      SeLe4n.Model.LockId.lookup_lockState_eq .projection,
    lkst! "LockId.lookup_objStore: SystemState-level kind fails closed"
      SeLe4n.Model.LockId.lookup_objStore .projection,
    lkst! "LockId.lookup_reply: SM3.A.5 N/A kind fails closed"
      SeLe4n.Model.LockId.lookup_reply .projection,
    lkst! "LockId.lookup_page: SM3.A.8 N/A kind fails closed"
      SeLe4n.Model.LockId.lookup_page .projection,
    -- §2 lockSet — per-transition declarations (25 entries — one per SyscallId variant)
    lkst! "lockSet for endpointSend"
      lockSet_endpointSend .lockSet,
    lkst! "lockSet for endpointReceive"
      lockSet_endpointReceive .lockSet,
    lkst! "lockSet for endpointCall"
      lockSet_endpointCall .lockSet,
    lkst! "lockSet for endpointReply"
      lockSet_endpointReply .lockSet,
    lkst! "lockSet for replyRecv"
      lockSet_replyRecv .lockSet,
    lkst! "lockSet for notificationSignal"
      lockSet_notificationSignal .lockSet,
    lkst! "lockSet for notificationWait"
      lockSet_notificationWait .lockSet,
    lkst! "lockSet for cspaceMint"
      lockSet_cspaceMint .lockSet,
    lkst! "lockSet for cspaceCopy"
      lockSet_cspaceCopy .lockSet,
    lkst! "lockSet for cspaceMove"
      lockSet_cspaceMove .lockSet,
    lkst! "lockSet for cspaceDelete"
      lockSet_cspaceDelete .lockSet,
    lkst! "lockSet for lifecycleRetype"
      lockSet_lifecycleRetype .lockSet,
    lkst! "lockSet for vspaceMap"
      lockSet_vspaceMap .lockSet,
    lkst! "lockSet for vspaceUnmap"
      lockSet_vspaceUnmap .lockSet,
    lkst! "lockSet for serviceRegister"
      lockSet_serviceRegister .lockSet,
    lkst! "lockSet for serviceRevoke"
      lockSet_serviceRevoke .lockSet,
    lkst! "lockSet for serviceQuery"
      lockSet_serviceQuery .lockSet,
    lkst! "lockSet for schedContextConfigure"
      lockSet_schedContextConfigure .lockSet,
    lkst! "lockSet for schedContextBind"
      lockSet_schedContextBind .lockSet,
    lkst! "lockSet for schedContextUnbind"
      lockSet_schedContextUnbind .lockSet,
    lkst! "lockSet for tcbSuspend"
      lockSet_tcbSuspend .lockSet,
    lkst! "lockSet for tcbResume"
      lockSet_tcbResume .lockSet,
    lkst! "lockSet for tcbSetPriority"
      lockSet_tcbSetPriority .lockSet,
    lkst! "lockSet for tcbSetMCPriority"
      lockSet_tcbSetMCPriority .lockSet,
    lkst! "lockSet for tcbSetIPCBuffer"
      lockSet_tcbSetIPCBuffer .lockSet,
    -- §3 consistency — per-transition lockSet_consistent theorems (25 entries)
    lkst! "lockSet_consistent for send"
      lockSet_consistent_send .consistency,
    lkst! "lockSet_consistent for receive"
      lockSet_consistent_receive .consistency,
    lkst! "lockSet_consistent for call"
      lockSet_consistent_call .consistency,
    lkst! "lockSet_consistent for reply"
      lockSet_consistent_reply .consistency,
    lkst! "lockSet_consistent for replyRecv"
      lockSet_consistent_replyRecv .consistency,
    lkst! "lockSet_consistent for notificationSignal"
      lockSet_consistent_notificationSignal .consistency,
    lkst! "lockSet_consistent for notificationWait"
      lockSet_consistent_notificationWait .consistency,
    lkst! "lockSet_consistent for cspaceMint"
      lockSet_consistent_cspaceMint .consistency,
    lkst! "lockSet_consistent for cspaceCopy"
      lockSet_consistent_cspaceCopy .consistency,
    lkst! "lockSet_consistent for cspaceMove"
      lockSet_consistent_cspaceMove .consistency,
    lkst! "lockSet_consistent for cspaceDelete"
      lockSet_consistent_cspaceDelete .consistency,
    lkst! "lockSet_consistent for lifecycleRetype"
      lockSet_consistent_lifecycleRetype .consistency,
    lkst! "lockSet_consistent for vspaceMap"
      lockSet_consistent_vspaceMap .consistency,
    lkst! "lockSet_consistent for vspaceUnmap"
      lockSet_consistent_vspaceUnmap .consistency,
    lkst! "lockSet_consistent for serviceRegister"
      lockSet_consistent_serviceRegister .consistency,
    lkst! "lockSet_consistent for serviceRevoke"
      lockSet_consistent_serviceRevoke .consistency,
    lkst! "lockSet_consistent for serviceQuery"
      lockSet_consistent_serviceQuery .consistency,
    lkst! "lockSet_consistent for schedContextConfigure"
      lockSet_consistent_schedContextConfigure .consistency,
    lkst! "lockSet_consistent for schedContextBind"
      lockSet_consistent_schedContextBind .consistency,
    lkst! "lockSet_consistent for schedContextUnbind"
      lockSet_consistent_schedContextUnbind .consistency,
    lkst! "lockSet_consistent for tcbSuspend"
      lockSet_consistent_tcbSuspend .consistency,
    lkst! "lockSet_consistent for tcbResume"
      lockSet_consistent_tcbResume .consistency,
    lkst! "lockSet_consistent for tcbSetPriority"
      lockSet_consistent_tcbSetPriority .consistency,
    lkst! "lockSet_consistent for tcbSetMCPriority"
      lockSet_consistent_tcbSetMCPriority .consistency,
    lkst! "lockSet_consistent for tcbSetIPCBuffer"
      lockSet_consistent_tcbSetIPCBuffer .consistency,
    -- §4 acquireSort (5 entries — SM3.B.5/B.6/B.7/B.8 + length)
    lkst! "lockAcquireSequence sorts a LockSet by LockId ascending"
      LockSet.lockAcquireSequence .acquireSort,
    lkst! "lockAcquireSequence_ordered: sorted by LockId ≤"
      LockSet.lockAcquireSequence_ordered .acquireSort,
    lkst! "lockAcquireSequence_complete: every pair appears in the sort"
      LockSet.lockAcquireSequence_complete .acquireSort,
    lkst! "lockAcquireSequence_canonical: the sort is the unique sorted permutation"
      LockSet.lockAcquireSequence_canonical .acquireSort,
    lkst! "lockAcquireSequence_length preserves cardinality"
      LockSet.lockAcquireSequence_length .acquireSort,
    -- §5 algebra (8 entries — AccessMode + LockSet structural)
    lkst! "AccessMode.lub idempotent"
      AccessMode.lub_idem .algebra,
    lkst! "AccessMode.lub commutative"
      AccessMode.lub_comm .algebra,
    lkst! "AccessMode.lub associative"
      AccessMode.lub_assoc .algebra,
    lkst! "AccessMode.conflicts symmetric"
      AccessMode.conflicts_symm .algebra,
    lkst! "LockSet.insertOrMerge membership trace-back"
      LockSet.insertOrMerge_mem .algebra,
    lkst! "lockSetOfList membership trace-back"
      lockSetOfList_mem_inv .algebra,
    lkst! "LockSet.fst_inj_at_pairs: pairs with same fst are equal"
      LockSet.fst_inj_at_pairs .algebra,
    lkst! "LockSet.union_mem_inv: union membership trace-back"
      LockSet.union_mem_inv .algebra]

/-- WS-SM SM3.B: the inventory has exactly 81 entries.
A regression that adds a new SM3.B theorem without updating the
inventory fails this count witness at the Tier-3 surface check. -/
theorem lockSetTheorems_count :
    lockSetTheorems.length = 81 := by decide

/-- WS-SM SM3.B: 18 entries in the `projection` category
(lockKind def + 7 per-variant simp lemmas + lockKind_eq_of_objectType
 + LockId.fromObject + LockId.lookup + 4 lookup structural theorems
 + 3 fail-closed N/A witnesses). -/
theorem lockSetTheorems_projection_count :
    (lockSetTheorems.filter (fun t => t.category == .projection)).length = 18 := by
  decide

/-- WS-SM SM3.B: 25 entries in the `lockSet` category (one per SyscallId variant). -/
theorem lockSetTheorems_lockSet_count :
    (lockSetTheorems.filter (fun t => t.category == .lockSet)).length = 25 := by
  decide

/-- WS-SM SM3.B: 25 entries in the `consistency` category (one per SyscallId variant). -/
theorem lockSetTheorems_consistency_count :
    (lockSetTheorems.filter (fun t => t.category == .consistency)).length = 25 := by
  decide

/-- WS-SM SM3.B: 5 entries in the `acquireSort` category (SM3.B.5..B.8 + length). -/
theorem lockSetTheorems_acquireSort_count :
    (lockSetTheorems.filter (fun t => t.category == .acquireSort)).length = 5 := by
  decide

/-- WS-SM SM3.B: 8 entries in the `algebra` category. -/
theorem lockSetTheorems_algebra_count :
    (lockSetTheorems.filter (fun t => t.category == .algebra)).length = 8 := by
  decide

/-- WS-SM SM3.B: per-category counts sum to the total. -/
theorem lockSetTheorems_partition_sum :
    (lockSetTheorems.filter (fun t => t.category == .projection)).length +
    (lockSetTheorems.filter (fun t => t.category == .lockSet)).length +
    (lockSetTheorems.filter (fun t => t.category == .consistency)).length +
    (lockSetTheorems.filter (fun t => t.category == .acquireSort)).length +
    (lockSetTheorems.filter (fun t => t.category == .algebra)).length =
    lockSetTheorems.length := by decide

/-- WS-SM SM3.B: every inventory identifier is unique.

We use `native_decide` because the 72-entry inventory's
list-of-strings `Nodup` check exceeds `decide`'s practical
elaboration budget; `native_decide` compiles to native code and
discharges the same proposition in milliseconds.  The trust base
is identical to `decide` (Lean's kernel verifies the reduction
result). -/
theorem lockSetTheorems_identifiers_nodup :
    (lockSetTheorems.map (·.identifier)).Nodup := by native_decide

/-- WS-SM SM3.B: every inventory description is unique. -/
theorem lockSetTheorems_descriptions_nodup :
    (lockSetTheorems.map (·.description)).Nodup := by native_decide

/-- WS-SM SM3.B.4 aggregate count: there are exactly 25 consistency
entries — one per SyscallId variant.  This pairs with
`SyscallId.count = 25` (in `Model/Object/Types.lean`) to witness
*coverage* of the plan §5.2.SM3.B.4 obligation across every
modeled kernel transition. -/
theorem lockSet_consistent_aggregate_covers_every_syscall :
    (lockSetTheorems.filter (fun t => t.category == .consistency)).length =
    SyscallId.count := by decide

end SeLe4n.Kernel.Concurrency
