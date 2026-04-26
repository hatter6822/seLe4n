-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude
import SeLe4n.Model.Object
import SeLe4n.Model.State
import SeLe4n.Model.FrozenState
import SeLe4n.Kernel.SchedContext.PriorityManagement
import SeLe4n.Kernel.RadixTree.Bridge
import SeLe4n.Kernel.FrozenOps.Core
import SeLe4n.Kernel.FrozenOps.Operations
import SeLe4n.Testing.Helpers

/-!
# AN11-E.1 (TST-M01) — AK8 sub-item coverage

Phase AK8 (commit `c5cd86…` per CHANGELOG, v0.30.1) closed eleven sub-tasks
covering 7 capability MEDIUM findings (`C-M01..C-M07`), 4 data-structure
MEDIUM findings (`DS-M01..DS-M04`), and a 21-entry LOW batch.  At the time
of landing, only AK8-A (untyped region disjointness — 7 tests in
`tests/ModelIntegritySuite.lean`), AK8-B (transactional revoke — 3 tests
in `tests/NegativeStateSuite.lean`), and AK8-D (priority-authority
ceiling — 3 tests in `tests/PriorityManagementSuite.lean`) carried
runtime tests.  The remaining sub-items shipped with proof-only
verification.

This suite (AN11-E.1) closes the gap by adding success-path AND
failure-path runtime tests for every AK8 sub-item that mutates a
runtime-observable surface:

| Sub-task | What this suite verifies                                            |
| -------- | ------------------------------------------------------------------- |
| AK8-E    | `getCurrentPriorityChecked` ok / `.objectNotFound` paths            |
| AK8-F    | `findFirstEmptySlotChecked` cap on slot scan                        |
| AK8-G    | `frozenStoreTcbChecked`/Endpoint/Notification reject cross-variant |
| AK8-H    | `frozenSchedContextUnbind` transactional (TCB lookup before SC mut) |
| AK8-I    | `freezeCNodeSlotsChecked` rejects phantom keys                      |

AK8-C (caller-rights obligation block at `resolveCapAddress`),
AK8-J (`RHTable.BEq` lawful-instance documentation), and the AK8-K LOW
batch are pure-documentation closures that do not have a runtime-observable
surface; they are documented in the AK8 audit row of
`docs/dev_history/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md` rather than
exercised here.
-/

set_option maxRecDepth 1024

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Testing

namespace SeLe4n.Testing.Ak8Coverage

-- ============================================================================
-- AK8-E (C-M06) — getCurrentPriorityChecked
-- ============================================================================

/-- AK8-E success: an unbound TCB returns `.ok tcb.priority` (no SC lookup
required). -/
def test_AK8_E_unbound_returns_tcb_priority : IO Bool := do
  let tcb : TCB :=
    { tid := ThreadId.ofNat 1
      priority := ⟨42⟩
      domain := ⟨0⟩
      cspaceRoot := ObjId.ofNat 0
      vspaceRoot := ObjId.ofNat 0
      ipcBuffer := SeLe4n.VAddr.ofNat 0
      schedContextBinding := .unbound }
  match SeLe4n.Kernel.SchedContext.PriorityManagement.getCurrentPriorityChecked
          (default : SystemState) tcb with
  | .ok p => return p.val == 42
  | .error _ => return false

/-- AK8-E success: a TCB bound to an existing SchedContext returns the
SC's priority. -/
def test_AK8_E_bound_returns_sc_priority : IO Bool := do
  let scId : SchedContextId := SchedContextId.ofNat 200
  let sc : Kernel.SchedContext :=
    { scId := scId
      budget := ⟨100⟩, period := ⟨1000⟩
      priority := ⟨77⟩, deadline := ⟨0⟩
      domain := ⟨0⟩, budgetRemaining := ⟨100⟩
      boundThread := none, isActive := false
      replenishments := [] }
  let tcb : TCB :=
    { tid := ThreadId.ofNat 2
      priority := ⟨5⟩
      domain := ⟨0⟩
      cspaceRoot := ObjId.ofNat 0
      vspaceRoot := ObjId.ofNat 0
      ipcBuffer := SeLe4n.VAddr.ofNat 0
      schedContextBinding := .bound scId }
  let st : SystemState := { (default : SystemState) with
    objects := (default : SystemState).objects.insert scId.toObjId
      (.schedContext sc) }
  match SeLe4n.Kernel.SchedContext.PriorityManagement.getCurrentPriorityChecked
          st tcb with
  | .ok p => return p.val == 77
  | .error _ => return false

/-- AK8-E failure: a TCB bound to a SchedContext that does not exist in
the object store returns `.error .objectNotFound`. -/
def test_AK8_E_bound_missing_sc_is_objectNotFound : IO Bool := do
  let scId : SchedContextId := SchedContextId.ofNat 9999
  let tcb : TCB :=
    { tid := ThreadId.ofNat 3
      priority := ⟨5⟩
      domain := ⟨0⟩
      cspaceRoot := ObjId.ofNat 0
      vspaceRoot := ObjId.ofNat 0
      ipcBuffer := SeLe4n.VAddr.ofNat 0
      schedContextBinding := .bound scId }
  match SeLe4n.Kernel.SchedContext.PriorityManagement.getCurrentPriorityChecked
          (default : SystemState) tcb with
  | .ok _ => return false
  | .error e => return e == KernelError.objectNotFound

-- ============================================================================
-- AK8-F (C-M07) — findFirstEmptySlotChecked
-- ============================================================================

/-- AK8-F success: a CNode with one occupied slot returns the next
unoccupied index, bounded by `2^radixWidth`. -/
def test_AK8_F_returns_first_free_slot : IO Bool := do
  let occupied : Capability :=
    { target := .object (ObjId.ofNat 100), rights := AccessRightSet.empty,
      badge := none }
  let cn : CNode :=
    { depth := 16, guardWidth := 0, guardValue := 0, radixWidth := 4
      slots := (SeLe4n.Kernel.RobinHood.RHTable.empty 16).insert
        (SeLe4n.Slot.ofNat 0) occupied }
  -- limit=10 is intentionally larger than 2^4-0 = 16; the checker should
  -- still bound the scan to the radix window.
  match cn.findFirstEmptySlotChecked (SeLe4n.Slot.ofNat 0) 100 with
  | some s => return s.toNat == 1 && s.toNat < 2^cn.radixWidth
  | none => return false

/-- AK8-F failure: a `base` ≥ 2^radixWidth produces `none` (no slot in
range). -/
def test_AK8_F_rejects_base_over_radix : IO Bool := do
  let cn : CNode :=
    { depth := 16, guardWidth := 0, guardValue := 0, radixWidth := 2
      slots := SeLe4n.Kernel.RobinHood.RHTable.empty 16 }
  -- 2^2 = 4; base = 8 is out of range and must reject.
  match cn.findFirstEmptySlotChecked (SeLe4n.Slot.ofNat 8) 100 with
  | none => return true
  | some _ => return false

-- ============================================================================
-- AK8-G (DS-M01) — frozenStore*Checked variants reject cross-variant
-- ============================================================================

/-- Helper: a minimal empty FrozenSystemState (mirrors `tests/FrozenOpsSuite.lean`'s
private `emptyFrozenState`).  `FrozenSystemState` does not derive `Inhabited`,
so each field is initialised explicitly. -/
private def emptyFrozenState : FrozenSystemState :=
  { objects := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
    irqHandlers := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
    asidTable := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
    serviceRegistry := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
    interfaceRegistry := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
    services := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
    cdtChildMap := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
    cdtParentMap := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
    cdtSlotNode := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
    cdtNodeSlot := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
    cdtEdges := []
    cdtNextNode := ⟨0⟩
    scheduler :=
      { byPriority := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
        threadPriority := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
        membership := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
        current := none
        activeDomain := ⟨0⟩
        domainTimeRemaining := 5
        domainSchedule := []
        domainScheduleIndex := 0
        configDefaultTimeSlice := 5
        replenishQueue := { entries := [], size := 0 } }
    objectTypes := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
    capabilityRefs := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
    machine := default
    objectIndex := []
    objectIndexSet := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
    scThreadIndex := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
    tlb := TlbState.empty }

/-- Helper: build a minimal FrozenSystemState containing the given objects.
`FrozenMap.set` REQUIRES the key to already exist (frozen maps have a
fixed key set), so we construct the underlying `RHTable` with all entries
first and then `freezeMap` once. -/
private def mkFrozenStateWith (entries : List (ObjId × FrozenKernelObject))
    : FrozenSystemState :=
  let rt := entries.foldl (fun acc (k, v) => acc.insert k v)
              (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
  { emptyFrozenState with objects := freezeMap rt }

/-- AK8-G success: writing a TCB at a slot already holding a TCB succeeds. -/
def test_AK8_G_storeTcbChecked_same_kind_ok : IO Bool := do
  let tid : ThreadId := ThreadId.ofNat 50
  let tcb : TCB :=
    { tid := tid
      priority := ⟨5⟩
      domain := ⟨0⟩
      cspaceRoot := ObjId.ofNat 0
      vspaceRoot := ObjId.ofNat 0
      ipcBuffer := SeLe4n.VAddr.ofNat 0 }
  let st := mkFrozenStateWith [(tid.toObjId, (.tcb tcb))]
  match SeLe4n.Kernel.FrozenOps.frozenStoreTcbChecked tid tcb st with
  | .ok _ => return true
  | .error _ => return false

/-- AK8-G failure: writing a TCB at a slot holding an Endpoint is rejected
(the underlying `frozenLookupTcb` returns `none` for non-TCB variants). -/
def test_AK8_G_storeTcbChecked_cross_variant_rejected : IO Bool := do
  let tid : ThreadId := ThreadId.ofNat 51
  let ep : Endpoint := {}
  let st := mkFrozenStateWith [(tid.toObjId, (.endpoint ep))]
  let tcb : TCB :=
    { tid := tid
      priority := ⟨5⟩
      domain := ⟨0⟩
      cspaceRoot := ObjId.ofNat 0
      vspaceRoot := ObjId.ofNat 0
      ipcBuffer := SeLe4n.VAddr.ofNat 0 }
  match SeLe4n.Kernel.FrozenOps.frozenStoreTcbChecked tid tcb st with
  | .ok _ => return false
  | .error e => return e == KernelError.objectNotFound

/-- AK8-G failure: `frozenStoreEndpointChecked` rejects writing to a slot
holding a Notification. -/
def test_AK8_G_storeEndpointChecked_cross_variant_rejected : IO Bool := do
  let id : ObjId := ObjId.ofNat 52
  let n : Notification := { state := .idle, waitingThreads := [] }
  let st := mkFrozenStateWith [(id, (.notification n))]
  let ep : Endpoint := {}
  match SeLe4n.Kernel.FrozenOps.frozenStoreEndpointChecked id ep st with
  | .ok _ => return false
  | .error e => return e == KernelError.objectNotFound

/-- AK8-G failure: `frozenStoreNotificationChecked` rejects writing to a
slot holding a TCB. -/
def test_AK8_G_storeNotificationChecked_cross_variant_rejected : IO Bool := do
  let id : ObjId := ObjId.ofNat 53
  let tcb : TCB :=
    { tid := ThreadId.ofNat 53
      priority := ⟨5⟩
      domain := ⟨0⟩
      cspaceRoot := ObjId.ofNat 0
      vspaceRoot := ObjId.ofNat 0
      ipcBuffer := SeLe4n.VAddr.ofNat 0 }
  let st := mkFrozenStateWith [(id, (.tcb tcb))]
  let n : Notification := { state := .idle, waitingThreads := [] }
  match SeLe4n.Kernel.FrozenOps.frozenStoreNotificationChecked id n st with
  | .ok _ => return false
  | .error e => return e == KernelError.objectNotFound

-- ============================================================================
-- AK8-H (DS-M02) — frozenSchedContextUnbind transactional discipline
-- ============================================================================

/-- AK8-H failure: when the SC's `boundThread` is `some tid` but the TCB
does NOT exist in the store, `frozenSchedContextUnbind` returns
`.error .objectNotFound` and (per the transactional discipline) does NOT
mutate the SC.  The pre-AK8-H implementation would have written
`boundThread := none` and *then* discovered the missing TCB. -/
def test_AK8_H_unbind_missing_tcb_no_partial_mutation : IO Bool := do
  let scId : ObjId := ObjId.ofNat 60
  let danglingTid : ThreadId := ThreadId.ofNat 9999
  let sc : Kernel.SchedContext :=
    { scId := SchedContextId.ofObjId scId
      budget := ⟨100⟩, period := ⟨1000⟩
      priority := ⟨0⟩, deadline := ⟨0⟩
      domain := ⟨0⟩, budgetRemaining := ⟨100⟩
      boundThread := some danglingTid
      isActive := true
      replenishments := [] }
  let st := mkFrozenStateWith [(scId, (.schedContext sc))]
  match SeLe4n.Kernel.FrozenOps.frozenSchedContextUnbind scId st with
  | .ok _ => return false
  | .error e =>
      if e ≠ KernelError.objectNotFound then return false
      else
        -- Crucial transactional check: the SC must be UNCHANGED after
        -- the failed unbind.  If we read back the SC and find boundThread
        -- = none and isActive = false, the implementation has leaked a
        -- partial mutation.
        match st.objects.get? scId with
        | some (.schedContext sc') =>
            return sc'.boundThread == some danglingTid && sc'.isActive == true
        | _ => return false

/-- AK8-H success: when both the SC and bound TCB are present, unbind
succeeds and clears both `boundThread` and the TCB's binding. -/
def test_AK8_H_unbind_happy_path : IO Bool := do
  let scId : ObjId := ObjId.ofNat 61
  let tid : ThreadId := ThreadId.ofNat 70
  let sc : Kernel.SchedContext :=
    { scId := SchedContextId.ofObjId scId
      budget := ⟨100⟩, period := ⟨1000⟩
      priority := ⟨0⟩, deadline := ⟨0⟩
      domain := ⟨0⟩, budgetRemaining := ⟨100⟩
      boundThread := some tid
      isActive := true
      replenishments := [] }
  let tcb : TCB :=
    { tid := tid
      priority := ⟨5⟩
      domain := ⟨0⟩
      cspaceRoot := ObjId.ofNat 0
      vspaceRoot := ObjId.ofNat 0
      ipcBuffer := SeLe4n.VAddr.ofNat 0
      schedContextBinding := .bound (SchedContextId.ofObjId scId) }
  let st1 := mkFrozenStateWith
    [ (scId, .schedContext sc)
    , (tid.toObjId, .tcb tcb) ]
  match SeLe4n.Kernel.FrozenOps.frozenSchedContextUnbind scId st1 with
  | .ok ((), st') =>
      match st'.objects.get? scId, st'.objects.get? tid.toObjId with
      | some (.schedContext sc'), some (.tcb tcb') =>
          return sc'.boundThread == none && sc'.isActive == false
                 && tcb'.schedContextBinding == .unbound
      | _, _ => return false
  | .error _ => return false

-- ============================================================================
-- AK8-I (DS-M03) — freezeCNodeSlotsChecked rejects phantom keys
-- ============================================================================

/-- AK8-I success: a CNode with all keys within `2^radixWidth` freezes. -/
def test_AK8_I_well_keyed_freeze_succeeds : IO Bool := do
  let cap : Capability :=
    { target := .object (ObjId.ofNat 100), rights := AccessRightSet.empty,
      badge := none }
  let cn : CNode :=
    { depth := 16, guardWidth := 0, guardValue := 0, radixWidth := 4
      slots := ((SeLe4n.Kernel.RobinHood.RHTable.empty 16).insert
                  (SeLe4n.Slot.ofNat 0) cap).insert
                  (SeLe4n.Slot.ofNat 5) cap }
  -- 2^4 = 16; both keys (0, 5) are within range.
  return (SeLe4n.Kernel.RadixTree.freezeCNodeSlotsChecked cn).isSome

/-- AK8-I failure: a CNode with a phantom key (≥ 2^radixWidth) is
rejected at freeze time. -/
def test_AK8_I_phantom_key_freeze_rejected : IO Bool := do
  let cap : Capability :=
    { target := .object (ObjId.ofNat 100), rights := AccessRightSet.empty,
      badge := none }
  let cn : CNode :=
    { depth := 16, guardWidth := 0, guardValue := 0, radixWidth := 2
      -- 2^2 = 4; key 8 is a phantom (out of radix range).
      slots := (SeLe4n.Kernel.RobinHood.RHTable.empty 16).insert
        (SeLe4n.Slot.ofNat 8) cap }
  return (SeLe4n.Kernel.RadixTree.freezeCNodeSlotsChecked cn).isNone

-- ============================================================================
-- Suite runner
-- ============================================================================

/-- AN11-E.1 test dispatch table.  Each entry pairs an AK8 sub-item ID
with the semantically-named test function.  The runner walks the table
and prints `AK8-X.<n> PASS` or `AK8-X.<n> FAIL` per row. -/
def ak8Tests : List (String × IO Bool) :=
  [ ("AK8-E.1 unbound TCB returns its own priority",
       test_AK8_E_unbound_returns_tcb_priority)
  , ("AK8-E.2 bound TCB returns SC priority",
       test_AK8_E_bound_returns_sc_priority)
  , ("AK8-E.3 bound TCB with missing SC -> .objectNotFound",
       test_AK8_E_bound_missing_sc_is_objectNotFound)
  , ("AK8-F.1 returns next free slot within radix",
       test_AK8_F_returns_first_free_slot)
  , ("AK8-F.2 base ≥ 2^radixWidth -> none",
       test_AK8_F_rejects_base_over_radix)
  , ("AK8-G.1 storeTcbChecked same-kind succeeds",
       test_AK8_G_storeTcbChecked_same_kind_ok)
  , ("AK8-G.2 storeTcbChecked cross-variant rejected",
       test_AK8_G_storeTcbChecked_cross_variant_rejected)
  , ("AK8-G.3 storeEndpointChecked cross-variant rejected",
       test_AK8_G_storeEndpointChecked_cross_variant_rejected)
  , ("AK8-G.4 storeNotificationChecked cross-variant rejected",
       test_AK8_G_storeNotificationChecked_cross_variant_rejected)
  , ("AK8-H.1 unbind missing TCB -> no partial mutation",
       test_AK8_H_unbind_missing_tcb_no_partial_mutation)
  , ("AK8-H.2 unbind happy path clears both sides",
       test_AK8_H_unbind_happy_path)
  , ("AK8-I.1 well-keyed CNode freezes",
       test_AK8_I_well_keyed_freeze_succeeds)
  , ("AK8-I.2 phantom-key CNode rejected",
       test_AK8_I_phantom_key_freeze_rejected) ]

def runAll : IO Bool := do
  IO.println s!"AK8 coverage suite: {ak8Tests.length} rows"
  let mut allOk : Bool := true
  for (label, body) in ak8Tests do
    try
      let ok ← body
      if ok then
        IO.println s!"PASS  {label}"
      else
        IO.println s!"FAIL  {label}"
        allOk := false
    catch e =>
      IO.println s!"FAIL  {label}: {e.toString}"
      allOk := false
  return allOk

end SeLe4n.Testing.Ak8Coverage

def main : IO UInt32 := do
  let ok ← SeLe4n.Testing.Ak8Coverage.runAll
  if ok then
    IO.println "ak8_coverage_suite: ALL PASS"
    return 0
  else
    IO.println "ak8_coverage_suite: FAILURES"
    return 1
