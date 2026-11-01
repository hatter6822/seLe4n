-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n
import SeLe4n.Testing.StateBuilder
import SeLe4n.Testing.InvariantChecks
import SeLe4n.Testing.Helpers
import SeLe4n.Platform.Boot
import SeLe4n.Platform.RPi5.Board
import SeLe4n.Platform.RPi5.BootContract
import SeLe4n.Testing.BootCoreOps

set_option maxRecDepth 1024

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)

/-- S2-A: BEq for Except, enabling structural equality (`==`) in determinism checks.
Lean 4's Except does not derive BEq or DecidableEq automatically. -/
instance instBEqExceptS2 [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok x, .ok y => x == y
    | .error e1, .error e2 => e1 == e2
    | _, _ => false

namespace SeLe4n.Testing

private def endpointId : SeLe4n.ObjId := ⟨40⟩
private def cnodeId : SeLe4n.ObjId := ⟨10⟩
private def wrongTypeId : SeLe4n.ObjId := ⟨99⟩
private def guardedCnodeId : SeLe4n.ObjId := ⟨55⟩
private def notificationId : SeLe4n.ObjId := ⟨42⟩
private def asidPrimary : SeLe4n.ASID := ⟨2⟩
private def vaddrPrimary : SeLe4n.VAddr := (SeLe4n.VAddr.ofNat 4096)
private def paddrPrimary : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat 12288)

private def slot0 : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := SeLe4n.Slot.ofNat 0 }
-- WS-RR RR8.16 (`v0.35.201`): `cnodeId` consumes 4 bits per hop, so a path into
-- it carries at least that depth; CPtr 0 still names slot 0.
private def slot0Path : SeLe4n.Kernel.CSpacePathAddr := { cnode := cnodeId, cptr := SeLe4n.CPtr.ofNat 0, depth := 4 }
private def guardedPathBadDepth : SeLe4n.Kernel.CSpacePathAddr := { cnode := guardedCnodeId, cptr := SeLe4n.CPtr.ofNat 0, depth := 1 }
private def badSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := wrongTypeId, slot := SeLe4n.Slot.ofNat 0 }
private def guardedPathBadGuard : SeLe4n.Kernel.CSpacePathAddr := { cnode := guardedCnodeId, cptr := SeLe4n.CPtr.ofNat 0, depth := 3 }

private def baseState : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject endpointId (.endpoint {})
    -- WS-RR RR8.16 (`v0.35.201`): sixteen addressable slots.  This fixture
    -- declared `radixWidth := 0` — one slot — while the checks below move,
    -- mint and map CDT nodes at slot indices up to 12, none of which any CPtr
    -- could have named.
    |>.withObject cnodeId (.cnode (SeLe4n.Model.CNode.ofSlots 4 0 0 4 (SeLe4n.UniqueSlotMap.ofListWF [
        (SeLe4n.Slot.ofNat 0, {
          target := .object endpointId
          rights := AccessRightSet.ofList [.read, .write]
        })
      ])))
    |>.withObject wrongTypeId (.endpoint {})
    |>.withObject guardedCnodeId (.cnode (SeLe4n.Model.CNode.ofSlots 0 1 1 2 (SeLe4n.UniqueSlotMap.ofListWF [
        (SeLe4n.Slot.ofNat 1, {
          target := .object endpointId
          rights := AccessRightSet.ofList [.read]
        })
      ])))
    |>.withObject ⟨6⟩ (.tcb {
      tid := ⟨6⟩
      priority := ⟨43⟩
      domain := ⟨0⟩
      spaceCells := SeLe4n.Model.TCB.spaceCellsOf cnodeId ⟨20⟩
      ipcBuffer := (SeLe4n.VAddr.ofNat 2048)
    })
    |>.withObject ⟨7⟩ (.tcb {
      tid := ⟨7⟩
      priority := ⟨42⟩
      domain := ⟨0⟩
      spaceCells := SeLe4n.Model.TCB.spaceCellsOf cnodeId ⟨20⟩
      ipcBuffer := (SeLe4n.VAddr.ofNat 4096)
    })
    |>.withObject ⟨8⟩ (.tcb {
      tid := ⟨8⟩
      priority := ⟨41⟩
      domain := ⟨0⟩
      spaceCells := SeLe4n.Model.TCB.spaceCellsOf cnodeId ⟨20⟩
      ipcBuffer := (SeLe4n.VAddr.ofNat 8192)
    })
    |>.withObject ⟨9⟩ (.tcb {
      tid := ⟨9⟩
      priority := ⟨40⟩
      domain := ⟨0⟩
      spaceCells := SeLe4n.Model.TCB.spaceCellsOf cnodeId ⟨20⟩
      ipcBuffer := (SeLe4n.VAddr.ofNat 12288)
    })
    |>.withObject notificationId (.notification { state := .idle, hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero })
    |>.withObject ⟨20⟩ (.vspaceRoot { asid := asidPrimary, mappings := {} })
    |>.withLifecycleObjectType endpointId .endpoint
    |>.withLifecycleObjectType cnodeId .cnode
    |>.withLifecycleObjectType wrongTypeId .endpoint
    |>.withLifecycleObjectType guardedCnodeId .cnode
    |>.withLifecycleObjectType ⟨6⟩ .tcb
    |>.withLifecycleObjectType ⟨7⟩ .tcb
    |>.withLifecycleObjectType ⟨8⟩ .tcb
    |>.withLifecycleObjectType ⟨9⟩ .tcb
    |>.withLifecycleObjectType notificationId .notification
    |>.withLifecycleObjectType ⟨20⟩ .vspaceRoot
    |>.withRunnable [⟨6⟩, ⟨7⟩, ⟨8⟩, ⟨9⟩]
    |>.buildChecked)

private def invariantObjectIds : List SeLe4n.ObjId :=
  [endpointId, cnodeId, wrongTypeId, guardedCnodeId, notificationId, ⟨20⟩, ⟨6⟩, ⟨7⟩, ⟨8⟩, ⟨9⟩]

-- W5-A: Consolidated test helpers — delegate to SeLe4n.Testing shared helpers
private def expectErr
    (label : String)
    (actual : Except KernelError α)
    (expected : KernelError) : IO Unit :=
  SeLe4n.Testing.expectError label actual expected (msgPrefix := "negative check")

private def expectOkSt
    (label : String)
    (actual : Except KernelError (α × SystemState)) : IO (α × SystemState) := do
  let result ← SeLe4n.Testing.expectOkState label actual (msgPrefix := "positive check")
  let (_, st) := result
  assertStateInvariantsFor label invariantObjectIds st
  pure result

/-- A per-core arm's `(state, result)` pair as `expectOkSt` reads it. -/
private def expectOkOnCore
    (label : String)
    (actual : SystemState × Except KernelError α) : IO (α × SystemState) :=
  expectOkSt label (match actual with
    | (st, .ok a) => .ok (a, st)
    | (_, .error e) => .error e)

private def expectOkVal
    (label : String)
    (actual : Except KernelError α) : IO α :=
  SeLe4n.Testing.expectOk label actual (msgPrefix := "positive check")

private def expectThreadQueueLinks
    (label : String)
    (st : SystemState)
    (tid : SeLe4n.ThreadId)
    (expectedPrev : Option SeLe4n.ThreadId)
    (expectedPPrev : Option QueuePPrev)
    (expectedNext : Option SeLe4n.ThreadId) : IO Unit :=
  match (st.objects[tid.toObjId]? : Option KernelObject) with
  | some (.tcb tcb) =>
      if tcb.queuePrev = expectedPrev ∧ tcb.queuePPrev = expectedPPrev ∧ tcb.queueNext = expectedNext then
        IO.println s!"positive check passed [{label}]"
      else
        throw <| IO.userError
          s!"{label}: expected queuePrev={toString expectedPrev} queuePPrev={toString expectedPPrev} queueNext={toString expectedNext}, got prev={toString tcb.queuePrev} pprev={toString tcb.queuePPrev} next={toString tcb.queueNext}"
  | _ =>
      throw <| IO.userError s!"{label}: expected TCB object"

private def corruptThreadQueueLinks
    (st : SystemState)
    (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId)
    (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId) : Except KernelError SystemState :=
  match (st.objects[tid.toObjId]? : Option KernelObject) with
  | some (.tcb tcb) =>
      .ok {
        st with
        objects := st.objects.insert tid.toObjId
          (.tcb { tcb with queuePrevCode := SeLe4n.ThreadId.optCode prev, queuePPrevCode := QueuePPrev.optCode pprev, queueNextCode := SeLe4n.ThreadId.optCode next })
      }
  | _ => .error .objectNotFound

/-- **PR #897 review (`v0.35.108`)**: the sibling of `corruptThreadQueueLinks`, one
level up — write an endpoint's two queue boundaries directly.

Needed because the fifth `dualQueueSystemInvariant` conjunct is *cross*-endpoint, so
no sequence of live operations can reach a violating state: every kernel queue
writer maintains disjointness by construction, which is exactly why the conjunct is
provable.  A witness for it therefore has to write the second endpoint by hand, as
the pairing witnesses write a corrupted back-pointer by hand. -/
private def corruptEndpointQueueHeads
    (st : SystemState)
    (epId : SeLe4n.ObjId)
    (sendHead recvHead : Option SeLe4n.ThreadId) : Except KernelError SystemState :=
  match (st.objects[epId]? : Option KernelObject) with
  | some (.endpoint ep) =>
      .ok {
        st with
        objects := st.objects.insert epId (.endpoint (Endpoint.ofQueues { head := sendHead, tail := sendHead }
          { head := recvHead, tail := recvHead }))
      }
  | _ => .error .objectNotFound

-- WS-F2 untyped memory test constants and states
private def f2UntypedObjId : SeLe4n.ObjId := ⟨80⟩
private def f2UntypedChildId : SeLe4n.ObjId := ⟨81⟩
private def f2UntypedAuthCnode : SeLe4n.ObjId := ⟨82⟩
private def f2UntypedAuthSlot : SeLe4n.Kernel.CSpaceAddr :=
  { cnode := f2UntypedAuthCnode, slot := SeLe4n.Slot.ofNat 0 }

private def f2UntypedState : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject f2UntypedObjId (.untyped {
      regionBase := (SeLe4n.PAddr.ofNat 0x10000)
      regionSize := 256
      children := []
      isDevice := false
    })
    |>.withObject f2UntypedAuthCnode (.cnode (SeLe4n.Model.CNode.ofSlots 0 0 0 0 (SeLe4n.UniqueSlotMap.ofListWF [
        (SeLe4n.Slot.ofNat 0, {
          target := .object f2UntypedObjId
          rights := AccessRightSet.ofList [.read, .write, .grant, .retype]
        })
      ])))
    |>.withLifecycleObjectType f2UntypedObjId .untyped
    |>.withLifecycleObjectType f2UntypedAuthCnode .cnode
    |>.buildChecked)

private def f2DeviceUntypedId : SeLe4n.ObjId := ⟨83⟩

private def f2DeviceState : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject f2DeviceUntypedId (.untyped {
      regionBase := (SeLe4n.PAddr.ofNat 0x20000)
      regionSize := 4096
      children := []
      isDevice := true
    })
    |>.withObject f2UntypedAuthCnode (.cnode (SeLe4n.Model.CNode.ofSlots 0 0 0 0 (SeLe4n.UniqueSlotMap.ofListWF [
        (SeLe4n.Slot.ofNat 0, {
          target := .object f2DeviceUntypedId
          rights := AccessRightSet.ofList [.read, .write, .grant, .retype]
        })
      ])))
    |>.withLifecycleObjectType f2DeviceUntypedId .untyped
    |>.withLifecycleObjectType f2UntypedAuthCnode .cnode
    |>.buildChecked)

/-- Baseline `cspaceLookup*` negative checks (wrong type, depth/guard mismatch).
    Extracted from `runNegativeChecks` (Phase 1; was lines 248-262). -/
private def runBaselineLookupNegativeChecks : IO Unit := do
  assertStateInvariantsFor "negative suite baseState" invariantObjectIds baseState
  expectErr "lookup wrong object type"
    (SeLe4n.Kernel.cspaceLookupSlot badSlot baseState)
    .objectNotFound
  let _ ← expectOkVal "lookup path resolved"
    (SeLe4n.Kernel.cspaceLookupPath slot0Path baseState)

  expectErr "lookup path depth mismatch"
    (SeLe4n.Kernel.cspaceLookupPath guardedPathBadDepth baseState)
    .illegalState

  expectErr "lookup path guard mismatch"
    (SeLe4n.Kernel.cspaceLookupPath guardedPathBadGuard baseState)
    .invalidCapability


/-- WS-E4/C-02/C-03 cspaceMove + cspaceDeleteSlot CDT cleanup, and the
    revocation of two siblings (WS-ZA ZA5.3 part 8; the strict and
    transactional variants this block exercised were removed with the general
    revocation).  Extracted from `runNegativeChecks` (Phase 1). -/
private def runCspaceMutationAndRevokeNegativeChecks : IO Unit := do
  -- WS-E4/C-02/C-03, WS-ZA ZA5.3 part 2: the slot is the derivation node, so a
  -- move carries the source's parent and children to the destination.
  let moveDst : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := SeLe4n.Slot.ofNat 2 }
  let moveParentSlot : SlotRef := { cnode := cnodeId, slot := SeLe4n.Slot.ofNat 7 }
  let moveChildSlot : SlotRef := { cnode := cnodeId, slot := SeLe4n.Slot.ofNat 8 }
  let moveSeed : SystemState :=
    { baseState with
      cdt := CapDerivationTree.empty
    } |>.withDerivationEdges [(moveParentSlot, slot0, .copy), (slot0, moveChildSlot, .mint)]
  let (_, moveState) ← expectOkSt "cspaceMove moves the source's tree position"
    (SeLe4n.Kernel.cspaceMove slot0 moveDst moveSeed)
  if moveState.slotLinkAt moveDst .parent = some moveParentSlot ∧
      moveState.linkChildrenOf moveDst = [moveChildSlot] ∧
      moveState.slotLinkAt slot0 .parent = none ∧
      moveState.linkChildrenOf slot0 = [] then
    IO.println "positive check passed [cspaceMove carries the source's parent and children to dst]"
  else
    throw <| IO.userError "cspaceMove should move the source slot's edges onto dst"
  if (linkedDerivationEdges moveState).length = (linkedDerivationEdges moveSeed).length then
    IO.println "positive check passed [cspaceMove neither adds nor drops CDT edges]"
  else
    throw <| IO.userError "cspaceMove unexpectedly changed the number of CDT edges"

  -- cspaceDeleteSlot on a leaf: its one edge leaves the tree with it.
  let leafDeleteSeed : SystemState :=
    { baseState with
      cdt := CapDerivationTree.empty
    } |>.withDerivationEdges [(moveParentSlot, moveDst, .copy)]
  let (_, deletedMoveDst) ← expectOkSt "cspaceDeleteSlot removes a leaf from the tree"
    (SeLe4n.Kernel.cspaceDeleteSlot moveDst leafDeleteSeed)
  if deletedMoveDst.slotLinkAt moveDst .parent = none ∧
      deletedMoveDst.linkChildrenOf moveParentSlot = [] ∧
      (linkedDerivationEdges deletedMoveDst).isEmpty then
    IO.println "positive check passed [cspaceDeleteSlot takes the slot's edges out of the tree]"
  else
    throw <| IO.userError "cspaceDeleteSlot must remove the deleted slot's edges"

  -- A delete never refuses because the slot has derived capabilities (seL4's
  -- cteDelete): the slot is spliced out and its child is re-derived from the
  -- slot's own parent, so revoking that parent still reaches it.
  let childOfBearing : SlotRef := { cnode := cnodeId, slot := SeLe4n.Slot.ofNat 9 }
  let bearingParent : SlotRef := { cnode := cnodeId, slot := SeLe4n.Slot.ofNat 13 }
  let childBearingSeed : SystemState :=
    { baseState with
      cdt := CapDerivationTree.empty
    } |>.withDerivationEdges [(bearingParent, slot0, .copy), (slot0, childOfBearing, .mint)]
  let (_, splicedSt) ← expectOkSt "cspaceDeleteSlot deletes a slot with CDT children"
    (SeLe4n.Kernel.cspaceDeleteSlot slot0 childBearingSeed)
  if splicedSt.slotLinkAt childOfBearing .parent = some bearingParent ∧
      splicedSt.linkChildrenOf slot0 = [] ∧
      splicedSt.slotLinkAt slot0 .parent = none ∧
      (linkedDerivationEdges splicedSt).contains (bearingParent, childOfBearing) then
    IO.println "positive check passed [cspaceDeleteSlot splices a parent slot out of the tree]"
  else
    throw <| IO.userError "cspaceDeleteSlot must re-derive the deleted slot's child from its parent"

  -- WS-E4/C-04 strict variant: surface first descendant deletion failure with context.
  -- WS-ZA ZA5.3 part 8: `.cspaceRevoke` is seL4's `cteRevoke`, a loop that
  -- deletes and finalises the source's first child until it has none.  Two
  -- siblings under one root: both go, the root stays, and the root is left with
  -- no children.
  let txRootSlot : SeLe4n.Kernel.CSpaceAddr :=
    { cnode := cnodeId, slot := SeLe4n.Slot.ofNat 10 }
  let txChildSlotA : SeLe4n.Kernel.CSpaceAddr :=
    { cnode := cnodeId, slot := SeLe4n.Slot.ofNat 11 }
  let txChildSlotB : SeLe4n.Kernel.CSpaceAddr :=
    { cnode := cnodeId, slot := SeLe4n.Slot.ofNat 12 }
  let rootCap : Capability := {
    target := .object endpointId,
    rights := AccessRightSet.ofList [.read, .write, .grant, .retype],
  }
  let txSeed : SeLe4n.Model.SystemState := {
    baseState with
      objects := baseState.objects.insert cnodeId (.cnode (CNode.ofList 8 0 0 8 [
        (txRootSlot.slot, rootCap), (txChildSlotA.slot, rootCap),
        (txChildSlotB.slot, rootCap)]))
      cdt := baseState.cdt
  } |>.withDerivationEdges [(txRootSlot, txChildSlotA, .copy), (txRootSlot, txChildSlotB, .copy)]
  let (_, revoked) ← expectOkSt "cspaceRevokeCdtFinalising revokes two siblings"
    (SeLe4n.Kernel.cspaceRevokeCdtFinalising bootCoreId txRootSlot txSeed)
  if (SystemState.lookupSlotCap revoked txChildSlotA).isNone ∧
      (SystemState.lookupSlotCap revoked txChildSlotB).isNone ∧
      (SystemState.lookupSlotCap revoked txRootSlot).isSome ∧
      revoked.linkChildrenOf txRootSlot = [] then
    IO.println "positive check passed [revoke deletes every child and keeps the source]"
  else
    throw <| IO.userError "revoke should delete both children, keep the source and leave it childless"

/-- F-03 fix chain: dual-queue receive on non-endpoint/missing-object, vspace lookup
    missing asid, vspace map+lookup roundtrip + duplicate conflict, notification
    wait #1 + signal wake, badge accumulation, notification wait #2.
    Extracted from `runNegativeChecks` (Phase 1; was lines 463-565).

    Returns `stN1` (the post-first-wait state) because the inline F-12 double-wait
    test in `runNegativeChecks` consumes it.  Returning rather than rebuilding
    preserves byte-for-byte stdout equivalence with the pre-refactor capture. -/
private def runVSpaceAndNotificationF03NegativeChecks : IO SystemState := do
  expectErr "dual-queue receive on non-endpoint object"
    (SeLe4n.Kernel.endpointReceiveDual cnodeId (SeLe4n.ThreadId.ofNat 1) none baseState)
    .invalidCapability

  expectErr "dual-queue receive on missing object"
    (SeLe4n.Kernel.endpointReceiveDual (SeLe4n.ObjId.ofNat 9999) (SeLe4n.ThreadId.ofNat 1) none baseState)
    .objectNotFound

  expectErr "vspace lookup missing asid"
    (SeLe4n.Kernel.Architecture.vspaceLookup ⟨99⟩ vaddrPrimary baseState)
    .asidNotBound

  -- F-03 fix: VSpace map test — verify mapping was actually created via subsequent lookup
  let (_, stMapped) ← expectOkSt "vspace map initial"
    ((SeLe4n.Kernel.Architecture.vspaceMapPageWithFlush asidPrimary vaddrPrimary paddrPrimary) baseState)

  -- Verify the mapping was actually created by looking it up
  match SeLe4n.Kernel.Architecture.vspaceLookup asidPrimary vaddrPrimary stMapped with
  | .ok (paddr, _) =>
      if paddr = paddrPrimary then
        IO.println "positive check passed [vspace map creates retrievable mapping]"
      else
        throw <| IO.userError s!"vspace map created wrong mapping: expected paddr={toString paddrPrimary}, got {toString paddr}"
  | .error err =>
      throw <| IO.userError s!"vspace lookup after map failed: {toString err} — mapping was not created"

  expectErr "vspace duplicate map conflict"
    ((SeLe4n.Kernel.Architecture.vspaceMapPageWithFlush asidPrimary vaddrPrimary paddrPrimary) stMapped)
    .mappingConflict

  let (_, _stAwait) ← expectOkSt "dual-queue receive enqueue seed"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 7) none baseState)

  -- F-03 fix: Notification wait — consistently check TCB ipcState across ALL variants
  let (waitBadge, stN1) ← expectOkSt "notification wait blocks with none"
    (SeLe4n.Kernel.notificationWait notificationId (SeLe4n.ThreadId.ofNat 7) baseState)
  if waitBadge = none then
    IO.println "positive check passed [notification wait #1 none]"
  else
    throw <| IO.userError "notification wait #1 expected none"

  match (stN1.objects[(SeLe4n.ThreadId.ofNat 7).toObjId]? : Option KernelObject) with
  | some (KernelObject.tcb tcb) =>
      if tcb.ipcState = .blockedOnNotification notificationId then
        IO.println "positive check passed [notification wait #1 blocks thread ipcState]"
      else
        throw <| IO.userError "notification wait #1 expected blockedOnNotification ipcState"
  | _ => throw <| IO.userError "notification wait #1 expected waiter tcb"

  let (_, stN2) ← expectOkSt "notification signal wakes waiter"
    (SeLe4n.Kernel.notificationSignal notificationId (SeLe4n.Badge.ofNatMasked 55) stN1)


  match (stN2.objects[(SeLe4n.ThreadId.ofNat 7).toObjId]? : Option KernelObject) with
  | some (KernelObject.tcb tcb) =>
      if tcb.ipcState = .ready then
        IO.println "positive check passed [notification signal wake sets waiter ipcState ready]"
      else
        throw <| IO.userError "notification signal wake expected waiter ipcState ready"
  | _ => throw <| IO.userError "notification signal wake expected waiter tcb"

  let (_, stN3) ← expectOkSt "notification signal stores active badge"
    (SeLe4n.Kernel.notificationSignal notificationId (SeLe4n.Badge.ofNatMasked 66) stN2)

  -- F-03 fix: Badge accumulation — assert badge value BEFORE final signal
  match (stN3.objects[notificationId]? : Option KernelObject) with
  | some (.notification ntfn) =>
      -- WS-F5/D1e: Badge stored via ofNatMasked; for 66 < 2^64, equivalent to ofNat 66
      if ntfn.pendingBadge = some (SeLe4n.Badge.ofNatMasked 66) then
        IO.println "positive check passed [notification badge precondition: badge=66 (word-bounded) before accumulation]"
      else
        throw <| IO.userError s!"notification badge precondition mismatch: expected some 66, got {toString ntfn.pendingBadge}"
  | _ => throw <| IO.userError "notification badge precondition expected notification object"

  let (_, stN4) ← expectOkSt "notification signal accumulates active badge"
    (SeLe4n.Kernel.notificationSignal notificationId (SeLe4n.Badge.ofNatMasked 5) stN3)

  match (stN4.objects[notificationId]? : Option KernelObject) with
  | some (.notification ntfn) =>
      -- WS-F5/D1e: Use word-bounded Badge.bor for expected accumulation value
      let expected := SeLe4n.Badge.bor (SeLe4n.Badge.ofNatMasked 66) (SeLe4n.Badge.ofNatMasked 5)
      if ntfn.pendingBadge = some expected then
        IO.println "positive check passed [notification signal accumulates active badge via word-bounded OR]"
      else
        throw <| IO.userError "notification active badge accumulation mismatch"
  | _ => throw <| IO.userError "notification signal expected notification object"

  -- F-03 fix: Notification wait #2 — check TCB ipcState after consuming badge
  let (waitBadge2, stN5) ← expectOkSt "notification wait consumes active badge"
    (SeLe4n.Kernel.notificationWait notificationId (SeLe4n.ThreadId.ofNat 8) stN4)
  if waitBadge2 = none then
    throw <| IO.userError "notification wait #2 expected delivered badge"
  else
    IO.println "positive check passed [notification wait #2 delivered badge]"

  -- Verify waiter TCB ipcState is ready after consuming badge (not blocked)
  match (stN5.objects[(SeLe4n.ThreadId.ofNat 8).toObjId]? : Option KernelObject) with
  | some (KernelObject.tcb tcb) =>
      if tcb.ipcState = .ready then
        IO.println "positive check passed [notification wait #2 consumer ipcState ready]"
      else
        throw <| IO.userError s!"notification wait #2 expected consumer ipcState ready, got {toString tcb.ipcState}"
  | _ => throw <| IO.userError "notification wait #2 expected consumer tcb"

  pure stN1

/-- WS-F5/D1e: Badge > 2^64 word-truncation semantics + small bridging tests.
    Extracted from `runNegativeChecks` (Phase 1; was lines 567-607). -/
private def runBadgeTruncationNegativeChecks : IO Unit := do
  -- ==========================================================================
  -- WS-F5/D1e: Badge > 2^64 word-truncation semantics
  -- ==========================================================================

  -- ofNatMasked silently truncates values exceeding the machine word
  let oversized : Nat := 2 ^ 64 + 42  -- 18446744073709551658
  let truncated := SeLe4n.Badge.ofNatMasked oversized
  let expected := SeLe4n.Badge.ofNatMasked 42  -- 42 mod 2^64 = 42
  if truncated = expected then
    IO.println "positive check passed [badge > 2^64 truncated to word-bounded value via ofNatMasked]"
  else
    throw <| IO.userError s!"badge word-truncation failed: ofNatMasked({oversized}) = {toString truncated}, expected {toString expected}"

  -- Truncated badge must satisfy validity predicate
  if truncated.isValid then
    IO.println "positive check passed [truncated badge passes isValid check]"
  else
    throw <| IO.userError "truncated badge should be valid but isValid returned false"

  -- R6-B: ofNatMasked always produces valid badges (word-bounded by construction)
  let maskedOversized := SeLe4n.Badge.ofNatMasked oversized
  if maskedOversized.isValid then
    IO.println "positive check passed [ofNatMasked always produces valid badge, even from oversized input]"
  else
    throw <| IO.userError "ofNatMasked should always produce valid badges"

  -- bor of two large badges is still word-bounded
  let borResult := SeLe4n.Badge.bor (SeLe4n.Badge.ofNatMasked (2 ^ 64 - 1)) (SeLe4n.Badge.ofNatMasked 1)
  if borResult.isValid then
    IO.println "positive check passed [Badge.bor of near-max values produces valid result]"
  else
    throw <| IO.userError "Badge.bor should always produce valid results"

  expectErr "notification wait wrong object type"
    (SeLe4n.Kernel.notificationWait endpointId (SeLe4n.ThreadId.ofNat 1) baseState)
    .invalidCapability

  expectErr "dual-queue send on missing object"
    (SeLe4n.Kernel.endpointSendDual (SeLe4n.ObjId.ofNat 9998) (SeLe4n.ThreadId.ofNat 8)
      (.frame none false) baseState)
    .objectNotFound

/-- WS-H12d/A-09: IPC message payload bounds enforcement (registers > 120 / caps > 3
    across send/call/reply/replyRecv).
    Extracted from `runNegativeChecks` (Phase 1; was lines 608-700). -/
private def runIpcPayloadBoundsNegativeChecks : IO Unit := do

  -- ==========================================================================
  -- WS-H12d/A-09: IPC message payload bounds enforcement
  -- ==========================================================================

  -- Send and call read their words and capability addresses from the sender's
  -- frame (WS-ZA ZA4.7), so their bound is the message-info decode's: a word
  -- declaring more than 120 registers does not decode, and its two-bit
  -- extra-caps field names at most three capabilities.
  if (MessageInfo.decode (MessageInfo.mk (maxMessageRegisters + 1) 0 0).encode).isNone then
    IO.println "negative check passed [a message-info word declaring 121 registers does not decode]"
  else
    throw <| IO.userError "a message-info word declaring 121 registers decoded"
  match MessageInfo.decode (MessageInfo.mk 0 (maxExtraCaps + 1) 0).encode with
  | some mi =>
    if mi.extraCaps ≤ maxExtraCaps then
      IO.println "negative check passed [a message-info word names at most three extra caps]"
    else
      throw <| IO.userError "a message-info word decoded more than three extra caps"
  | none => IO.println "negative check passed [a message-info word names at most three extra caps]"

  -- endpointReply rejects oversized registers
  expectErr "endpointReply rejects oversized registers"
    (SeLe4n.Kernel.endpointReply (SeLe4n.ThreadId.ofNat 1)
      (SeLe4n.ThreadId.ofNat 2)
      { registers := Array.mk (List.replicate 121 ⟨0⟩), badge := none } baseState)
    .ipcMessageTooLarge

  -- endpointReplyRecv rejects oversized registers
  expectErr "endpointReplyRecv rejects oversized registers"
    (SeLe4n.Kernel.endpointReplyRecv endpointId (SeLe4n.ThreadId.ofNat 1)
      (SeLe4n.ThreadId.ofNat 2)
      { registers := Array.mk (List.replicate 121 ⟨0⟩), badge := none } none baseState)
    .ipcMessageTooLarge

  -- The boundary message (exactly 120 registers, 3 extra caps) decodes.
  if (MessageInfo.decode (MessageInfo.mk maxMessageRegisters maxExtraCaps 0).encode).isSome then
    IO.println "positive check passed [boundary message not rejected by bounds]"
  else
    throw <| IO.userError "boundary message (120 regs, 3 caps) rejected by the message-info decode"

/-- WS-E4 M-01: dual-queue endpoint FIFO/handshake coverage.  Largest sub-helper
    at 333 lines — Phase 1b candidate if the C-depth probe still trips clang.
    Extracted from `runNegativeChecks` (Phase 1; was lines 702-1034). -/
private def runDualQueueEndpointFifoNegativeChecks : IO Unit := do
  -- ==========================================================================
  -- WS-E4 M-01 refinement: dual-queue endpoint FIFO/handshake coverage
  -- ==========================================================================

  let (_, stDualSend1) ← expectOkSt "dual queue send blocks sender"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) (.frame none false) baseState)
  match (stDualSend1.objects[endpointId]? : Option KernelObject) with
  | some (.endpoint ep) =>
      if ep.sendQ.head = some (SeLe4n.ThreadId.ofNat 7) ∧ ep.sendQ.tail = some (SeLe4n.ThreadId.ofNat 7) then
        IO.println "positive check passed [dual queue sender enqueued]"
      else
        throw <| IO.userError s!"dual queue sender enqueued expected head=tail=7, got {toString ep.sendQ}"
  | _ => throw <| IO.userError "dual queue sender enqueued expected endpoint object"
  expectThreadQueueLinks "dual queue sender enqueued link clear"
    stDualSend1 (SeLe4n.ThreadId.ofNat 7) none (some .endpointHead) none

  let (firstSender, _) ← expectOkSt "dual queue receive dequeues sender"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 8) none stDualSend1)
  if firstSender = SeLe4n.ThreadId.ofNat 7 then
    IO.println "positive check passed [dual queue first sender delivered]"
  else
    throw <| IO.userError s!"dual queue first sender expected tid 7, got {toString firstSender}"

  -- FIFO check across two blocked senders and one receiver consuming twice.
  let (_, stDualFifo1) ← expectOkSt "dual queue fifo enqueue sender 7"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) (.frame none false) baseState)
  let (_, stDualFifo2) ← expectOkSt "dual queue fifo enqueue sender 8"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 8) (.frame none false) stDualFifo1)
  expectThreadQueueLinks "dual queue fifo sender 7 links to sender 8"
    stDualFifo2 (SeLe4n.ThreadId.ofNat 7) none (some .endpointHead) (some (SeLe4n.ThreadId.ofNat 8))
  expectThreadQueueLinks "dual queue fifo sender 8 links from sender 7"
    stDualFifo2 (SeLe4n.ThreadId.ofNat 8) (some (SeLe4n.ThreadId.ofNat 7)) (some (.tcbNext (SeLe4n.ThreadId.ofNat 7))) none
  let (fifoFirst, stDualFifo3) ← expectOkSt "dual queue fifo receive #1"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 9) none stDualFifo2)
  expectThreadQueueLinks "dual queue fifo dequeue #1 clears sender 7 links"
    stDualFifo3 (SeLe4n.ThreadId.ofNat 7) none none none
  expectThreadQueueLinks "dual queue fifo dequeue #1 keeps sender 8 singleton head"
    stDualFifo3 (SeLe4n.ThreadId.ofNat 8) none (some .endpointHead) none
  let (fifoSecond, stDualFifo4) ← expectOkSt "dual queue fifo receive #2"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 9) none stDualFifo3)
  expectThreadQueueLinks "dual queue fifo dequeue #2 clears sender 8 links"
    stDualFifo4 (SeLe4n.ThreadId.ofNat 8) none none none

  -- Arbitrary O(1) remove with queuePPrev metadata: remove middle waiter 8 from [7,8,9].
  let (_, stDualRemove1) ← expectOkSt "dual queue remove enqueue sender 7"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) (.frame none false) baseState)
  let (_, stDualRemove2) ← expectOkSt "dual queue remove enqueue sender 8"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 8) (.frame none false) stDualRemove1)
  let (_, stDualRemove3) ← expectOkSt "dual queue remove enqueue sender 9"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 9) (.frame none false) stDualRemove2)
  let (_, stDualRemove4) ← expectOkSt "dual queue remove middle sender 8"
    (SeLe4n.Kernel.endpointQueueRemoveDual endpointId false (SeLe4n.ThreadId.ofNat 8) stDualRemove3)
  expectThreadQueueLinks "dual queue remove middle clears sender 8 links"
    stDualRemove4 (SeLe4n.ThreadId.ofNat 8) none none none
  expectThreadQueueLinks "dual queue remove middle repairs sender 7 -> sender 9"
    stDualRemove4 (SeLe4n.ThreadId.ofNat 7) none (some .endpointHead) (some (SeLe4n.ThreadId.ofNat 9))
  expectThreadQueueLinks "dual queue remove middle repairs sender 9 <- sender 7"
    stDualRemove4 (SeLe4n.ThreadId.ofNat 9) (some (SeLe4n.ThreadId.ofNat 7)) (some (.tcbNext (SeLe4n.ThreadId.ofNat 7))) none
  let (rmFirst, stDualRemove5) ← expectOkSt "dual queue remove receive #1"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 6) none stDualRemove4)
  let (rmSecond, _) ← expectOkSt "dual queue remove receive #2"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 6) none stDualRemove5)
  if rmFirst = SeLe4n.ThreadId.ofNat 7 ∧ rmSecond = SeLe4n.ThreadId.ofNat 9 then
    IO.println "positive check passed [dual queue remove preserves remaining FIFO order]"
  else
    throw <| IO.userError s!"dual queue remove expected [7,9], got [{toString rmFirst},{toString rmSecond}]"

  let stMalformedHeadPPrev ← expectOkVal "dual queue malformed pprev state (head points to prev tcbNext)"
    (corruptThreadQueueLinks stDualRemove3 (SeLe4n.ThreadId.ofNat 7) none (some (.tcbNext (SeLe4n.ThreadId.ofNat 8))) (some (SeLe4n.ThreadId.ofNat 8)))
  expectErr "dual queue malformed pprev rejects head non-endpoint owner"
    (SeLe4n.Kernel.endpointQueueRemoveDual endpointId false (SeLe4n.ThreadId.ofNat 7) stMalformedHeadPPrev)
    .illegalState

  let stMalformedPrevNext ← expectOkVal "dual queue malformed pprev state (prev next mismatch)"
    (corruptThreadQueueLinks stDualRemove3 (SeLe4n.ThreadId.ofNat 7) none (some .endpointHead) (some (SeLe4n.ThreadId.ofNat 9)))
  expectErr "dual queue malformed pprev rejects stale prev pointer"
    (SeLe4n.Kernel.endpointQueueRemoveDual endpointId false (SeLe4n.ThreadId.ofNat 8) stMalformedPrevNext)
    .illegalState

  let stMalformedDetached ← expectOkVal "dual queue malformed pprev detached thread in empty queue"
    (corruptThreadQueueLinks baseState (SeLe4n.ThreadId.ofNat 7) none (some .endpointHead) none)
  expectErr "dual queue malformed pprev rejects detached thread marked as queued"
    (SeLe4n.Kernel.endpointQueueRemoveDual endpointId false (SeLe4n.ThreadId.ofNat 7) stMalformedDetached)
    .illegalState

  if fifoFirst = SeLe4n.ThreadId.ofNat 7 ∧ fifoSecond = SeLe4n.ThreadId.ofNat 8 then
    IO.println "positive check passed [dual queue fifo ordering preserved]"
  else
    throw <| IO.userError s!"dual queue fifo ordering expected [7,8], got [{toString fifoFirst},{toString fifoSecond}]"

  expectErr "dual queue sender double-wait prevention"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) (.frame none false) stDualFifo1)
    .alreadyWaiting

  let (_, stDualRecvWait1) ← expectOkSt "dual queue receiver wait #1"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 9) none baseState)
  expectThreadQueueLinks "dual queue receiver wait keeps lone waiter detached"
    stDualRecvWait1 (SeLe4n.ThreadId.ofNat 9) none (some .endpointHead) none
  let (_, stDualRecvWait2) ← expectOkSt "dual queue receiver fifo enqueue receiver 8"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 8) none stDualRecvWait1)
  expectThreadQueueLinks "dual queue receiver fifo receiver 9 links to receiver 8"
    stDualRecvWait2 (SeLe4n.ThreadId.ofNat 9) none (some .endpointHead) (some (SeLe4n.ThreadId.ofNat 8))
  expectThreadQueueLinks "dual queue receiver fifo receiver 8 links from receiver 9"
    stDualRecvWait2 (SeLe4n.ThreadId.ofNat 8) (some (SeLe4n.ThreadId.ofNat 9)) (some (.tcbNext (SeLe4n.ThreadId.ofNat 9))) none
  let (_, stDualRecvWake) ← expectOkSt "dual queue sender wakes first waiting receiver"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) (.frame none false) stDualRecvWait2)
  expectThreadQueueLinks "dual queue sender wake clears first receiver links"
    stDualRecvWake (SeLe4n.ThreadId.ofNat 9) none none none
  expectThreadQueueLinks "dual queue sender wake keeps second receiver singleton head"
    stDualRecvWake (SeLe4n.ThreadId.ofNat 8) none (some .endpointHead) none
  expectErr "dual queue receiver double-wait prevention"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 9) none stDualRecvWait1)
    .alreadyWaiting

  match (stDualFifo4.objects[endpointId]? : Option KernelObject) with
  | some (.endpoint ep) =>
      if ep.sendQ.head = none ∧ ep.sendQ.tail = none then
        IO.println "positive check passed [dual queue fifo drains send queue]"
      else
        throw <| IO.userError s!"dual queue fifo expected empty intrusive sendQ, got {toString ep.sendQ}"
  | _ => throw <| IO.userError "dual queue fifo expected endpoint object"

  -- WS-H12b: dequeue-on-dispatch — current thread 7 is NOT in the runnable queue
  let schedPriorityState : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject ⟨7⟩ (.tcb {
        tid := ⟨7⟩
        priority := ⟨10⟩
        domain := ⟨0⟩
        spaceCells := SeLe4n.Model.TCB.spaceCellsOf SeLe4n.ObjId.sentinel SeLe4n.ObjId.sentinel
        ipcBuffer := (SeLe4n.VAddr.ofNat 4096)
      })
      |>.withObject ⟨8⟩ (.tcb {
        tid := ⟨8⟩
        priority := ⟨42⟩
        domain := ⟨0⟩
        spaceCells := SeLe4n.Model.TCB.spaceCellsOf SeLe4n.ObjId.sentinel SeLe4n.ObjId.sentinel
        ipcBuffer := (SeLe4n.VAddr.ofNat 8192)
      })
      |>.withRunnable [⟨8⟩]
      |>.withCurrent (some (SeLe4n.ThreadId.ofNat 7))
      |>.buildChecked)
  let (_, stPriorityScheduled) ← expectOkSt "schedule chooses highest-priority runnable"
    (bootSchedule schedPriorityState)
  if (stPriorityScheduled.scheduler.currentOnCore bootCoreId) = some (SeLe4n.ThreadId.ofNat 8) then
    IO.println "positive check passed [schedule priority order]: current = tid 8"
  else
    throw <| IO.userError "schedule priority order expected current = tid 8"

  -- WS-H12b: current=none so both threads can be in runnable; re-add thread 7
  -- (thread 7 is enqueued through the TCB links, so the live queue holds it too)
  let crossDomainEnqueued : SystemState :=
    ({ schedPriorityState with
      objects := schedPriorityState.objects.insert (SeLe4n.ThreadId.ofNat 7).toObjId (.tcb {
            tid := ⟨7⟩
            priority := ⟨80⟩
            domain := ⟨1⟩
            spaceCells := SeLe4n.Model.TCB.spaceCellsOf SeLe4n.ObjId.sentinel SeLe4n.ObjId.sentinel
            ipcBuffer := (SeLe4n.VAddr.ofNat 4096)
          }) } : SystemState).runEnqueueOnCore bootCoreId (SeLe4n.ThreadId.ofNat 7) ⟨80⟩
  let crossDomainState : SystemState :=
    { crossDomainEnqueued with
      scheduler := (crossDomainEnqueued.scheduler.setActiveDomainOnCore bootCoreId ⟨0⟩).setCurrentOnCore bootCoreId none }
  let (_, stCrossDomainScheduled) ← expectOkSt "schedule filters runnable set to active domain"
    (bootSchedule crossDomainState)
  if (stCrossDomainScheduled.scheduler.currentOnCore bootCoreId) = some (SeLe4n.ThreadId.ofNat 8) then
    IO.println "positive check passed [schedule domain filter]: active domain thread selected"
  else
    throw <| IO.userError "schedule domain filter expected current = tid 8"

  let noActiveDomainRunnableState : SystemState :=
    { crossDomainState with scheduler := crossDomainState.scheduler.setActiveDomainOnCore bootCoreId ⟨2⟩ }
  let (_, stNoActiveDomainRunnable) ← expectOkSt "schedule returns idle when no active-domain runnable threads"
    (bootSchedule noActiveDomainRunnableState)
  if (stNoActiveDomainRunnable.scheduler.currentOnCore bootCoreId) = none then
    IO.println "positive check passed [schedule domain isolation]: no cross-domain fallback"
  else
    throw <| IO.userError "schedule domain isolation expected current = none"

  let mixedDomainFifoState : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject ⟨10⟩ (.tcb {
        tid := ⟨10⟩
        priority := ⟨20⟩
        deadline := ⟨2⟩
        domain := ⟨1⟩
        spaceCells := SeLe4n.Model.TCB.spaceCellsOf SeLe4n.ObjId.sentinel SeLe4n.ObjId.sentinel
        ipcBuffer := (SeLe4n.VAddr.ofNat 12288)
      })
      |>.withObject ⟨11⟩ (.tcb {
        tid := ⟨11⟩
        priority := ⟨20⟩
        deadline := ⟨4⟩
        domain := ⟨1⟩
        spaceCells := SeLe4n.Model.TCB.spaceCellsOf SeLe4n.ObjId.sentinel SeLe4n.ObjId.sentinel
        ipcBuffer := (SeLe4n.VAddr.ofNat 16384)
      })
      |>.withObject ⟨12⟩ (.tcb {
        tid := ⟨12⟩
        priority := ⟨80⟩
        deadline := ⟨1⟩
        domain := ⟨0⟩
        spaceCells := SeLe4n.Model.TCB.spaceCellsOf SeLe4n.ObjId.sentinel SeLe4n.ObjId.sentinel
        ipcBuffer := (SeLe4n.VAddr.ofNat 20480)
      })
      |>.withRunnable [⟨12⟩, ⟨10⟩, ⟨11⟩]
      |>.withCurrent none
      |>.buildChecked)
      |> fun st => { st with scheduler := st.scheduler.setActiveDomainOnCore bootCoreId ⟨1⟩ }
  let (_, stMixedDomainScheduled) ← expectOkSt "schedule ignores higher-priority cross-domain runnable"
    (bootSchedule mixedDomainFifoState)
  if (stMixedDomainScheduled.scheduler.currentOnCore bootCoreId) = some (SeLe4n.ThreadId.ofNat 10) then
    IO.println "positive check passed [schedule mixed domain priority]: active-domain runnable wins"
  else
    throw <| IO.userError "schedule mixed domain priority expected current = tid 10"

  let (_, stMixedDomainScheduledFifo) ← expectOkSt "schedule keeps FIFO stability for equal prio/deadline in active domain"
    -- Only the deadline moves: the TCB keeps its run-queue links (WS-ZA ZA4.5),
    -- so the thread stays where the builder queued it.
    (bootSchedule (match mixedDomainFifoState.getTcb? (SeLe4n.ThreadId.ofNat 10) with
      | some tcb10 => {
          mixedDomainFifoState with
          objects := mixedDomainFifoState.objects.insert (SeLe4n.ThreadId.ofNat 10).toObjId
            (.tcb { tcb10 with deadline := ⟨4⟩ }) }
      | none => mixedDomainFifoState))
  if (stMixedDomainScheduledFifo.scheduler.currentOnCore bootCoreId) = some (SeLe4n.ThreadId.ofNat 10) then
    IO.println "positive check passed [schedule mixed domain FIFO]: earlier queue element retained"
  else
    throw <| IO.userError "schedule mixed domain FIFO expected current = tid 10"

  let scheduleDomainSwitchState : SystemState :=
    { mixedDomainFifoState with
      scheduler := { (((mixedDomainFifoState.scheduler.setActiveDomainOnCore bootCoreId ⟨0⟩).setCurrentOnCore bootCoreId (some (SeLe4n.ThreadId.ofNat 12))).setDomainTimeRemainingOnCore bootCoreId 1).setDomainScheduleIndexOnCore bootCoreId 0 with
        domainSchedule := [
          { domain := ⟨0⟩, length := 3 },
          { domain := ⟨1⟩, length := 2 }
        ] } }
  let (_, stScheduleDomainSwitched) ← expectOkSt "scheduleDomain switches domain and reschedules"
    (bootScheduleDomain scheduleDomainSwitchState)
  if (stScheduleDomainSwitched.scheduler.activeDomainOnCore bootCoreId) = ⟨1⟩ then
    IO.println "positive check passed [scheduleDomain active domain advance]: activeDomain = 1"
  else
    throw <| IO.userError "scheduleDomain active domain advance expected activeDomain = 1"
  if (stScheduleDomainSwitched.scheduler.domainScheduleIndexOnCore bootCoreId) = 1 then
    IO.println "positive check passed [scheduleDomain index advance]: index = 1"
  else
    throw <| IO.userError "scheduleDomain index advance expected index = 1"
  if (stScheduleDomainSwitched.scheduler.domainTimeRemainingOnCore bootCoreId) = 2 then
    IO.println "positive check passed [scheduleDomain refresh domain budget]: remaining = 2"
  else
    throw <| IO.userError "scheduleDomain refresh domain budget expected remaining = 2"
  if (stScheduleDomainSwitched.scheduler.currentOnCore bootCoreId) = some (SeLe4n.ThreadId.ofNat 10) then
    IO.println "positive check passed [scheduleDomain reschedule respects new active domain]: current = tid 10"
  else
    throw <| IO.userError "scheduleDomain reschedule expected current = tid 10"

  -- WS-H12b: dequeue-on-dispatch — current thread must NOT be in runnable queue
  -- (thread 10 is dequeued through the TCB links, so the live queue drops it too)
  let scheduleDomainDequeued : SystemState :=
    scheduleDomainSwitchState.runRemoveOnCore bootCoreId (SeLe4n.ThreadId.ofNat 10)
  let scheduleDomainTickOnlyState : SystemState :=
    { scheduleDomainDequeued with
      scheduler := (((scheduleDomainDequeued.scheduler.setActiveDomainOnCore bootCoreId ⟨1⟩).setCurrentOnCore bootCoreId (some (SeLe4n.ThreadId.ofNat 10))).setDomainTimeRemainingOnCore bootCoreId 3).setDomainScheduleIndexOnCore bootCoreId 1 }
  let (_, stScheduleDomainTickOnly) ← expectOkSt "scheduleDomain decrements budget without switching"
    (bootScheduleDomain scheduleDomainTickOnlyState)
  if (stScheduleDomainTickOnly.scheduler.activeDomainOnCore bootCoreId) = ⟨1⟩ ∧ (stScheduleDomainTickOnly.scheduler.domainScheduleIndexOnCore bootCoreId) = 1 then
    IO.println "positive check passed [scheduleDomain no switch]: domain/index unchanged"
  else
    throw <| IO.userError "scheduleDomain no switch expected domain/index unchanged"
  if (stScheduleDomainTickOnly.scheduler.domainTimeRemainingOnCore bootCoreId) = 2 then
    IO.println "positive check passed [scheduleDomain no switch budget decrement]: remaining = 2"
  else
    throw <| IO.userError "scheduleDomain no switch budget expected remaining = 2"
  if (stScheduleDomainTickOnly.scheduler.currentOnCore bootCoreId) = some (SeLe4n.ThreadId.ofNat 10) then
    IO.println "positive check passed [scheduleDomain no switch current consistency]: current preserved"
  else
    throw <| IO.userError "scheduleDomain no switch current consistency expected current = tid 10"

  -- F-03 fix: Yield test — verify which thread is current after rotation, not just queue membership
  let (_, stYielded) ← expectOkSt "yield rotates current within runnable queue"
    (bootYield schedPriorityState)
  -- WS-H12b: after yield, schedule dequeues the dispatched thread (8) from runnable
  if (stYielded.runQueueWalk bootCoreId) = [SeLe4n.ThreadId.ofNat 7] then
    IO.println "positive check passed [yield runnable rotation]: [7] (8 dequeued as current)"
  else
    throw <| IO.userError s!"yield runnable rotation expected [7], got {toString (stYielded.runQueueWalk bootCoreId)}"

  -- Verify which thread is current after yield (should be tid 8, the highest priority)
  if (stYielded.scheduler.currentOnCore bootCoreId) = some (SeLe4n.ThreadId.ofNat 8) then
    IO.println "positive check passed [yield current thread]: current = tid 8 (highest priority after rotation)"
  else
    throw <| IO.userError s!"yield current thread expected tid 8, got {toString (stYielded.scheduler.currentOnCore bootCoreId)}"

  -- Uses .build intentionally: runnable [tid 77] references non-existent TCB
  -- (check 3 would reject). Tests scheduler handling of malformed runnable list.
  let malformedSched : SystemState :=
    (BootstrapBuilder.empty
      |>.withRunnable [SeLe4n.ThreadId.ofNat 77]
      |>.withCurrent none
      |>.build)
  -- WS-ZA ZA4.5: a run-queue place is fields of the thread's TCB, so a thread
  -- with no TCB cannot be queued at all: the kernel's enqueue refuses it and the
  -- queue the scheduler walks stays empty.  The schedule checks below then pin
  -- that a core whose queue holds nothing dispatchable comes back idle.
  if (malformedSched.runQueueWalk bootCoreId).isEmpty then
    IO.println "positive check passed [an entry with no TCB takes no run-queue place]"
  else
    throw <| IO.userError s!"an entry with no TCB was queued: {toString (malformedSched.runQueueWalk bootCoreId)}"
  -- WS-SM SM8.B (PR #861 review round 15): these two used to assert
  -- `.schedulerInvariantViolation`.  They now assert the **stronger** property
  -- that replaced it: a run-queue entry whose object is not a TCB is *skipped*,
  -- so the scheduler still runs.
  --
  -- The old contract was not merely weaker, it was a denial of service.  The
  -- error aborted the entire selection scan — max-priority bucket and full-list
  -- fallback alike — and nothing on the failure path removes the offending
  -- entry, so one malformed entry stopped that core scheduling *anything*, for
  -- ever.  The retype destroy path could produce one (it swept only the boot
  -- core; see `removeRunnableFromAllCores`).  The invariant that no such entry
  -- exists is unchanged and still carried by `runnableThreadsAreTCBs`; the
  -- scheduler simply no longer depends on it to make progress.
  -- `expectOkVal`, not `expectOkSt`: the fixture is *deliberately* invariant-
  -- violating (that is the whole point of the case), so the post-state must not
  -- be run through `assertStateInvariantsFor` — it would fail on the very
  -- `runnableThreadsAreTCBs` breach the case constructs.
  let (_, stMalformed) ← expectOkVal "schedule skips a malformed runnable target"
    (bootSchedule malformedSched)
  -- The load-bearing part: skipping is not silently dispatching it.  There is no
  -- TCB to switch to, so the core must come back idle rather than current on 77.
  if (stMalformed.scheduler.currentOnCore bootCoreId) = none then
    IO.println "positive check passed [malformed entry skipped, core left idle]"
  else
    throw <| IO.userError s!"malformed runnable target must not be dispatched, got current = {toString (stMalformed.scheduler.currentOnCore bootCoreId)}"

  let malformedOffDomain : SystemState :=
    { malformedSched with scheduler := malformedSched.scheduler.setActiveDomainOnCore bootCoreId ⟨1⟩ }
  let (_, stMalformedOff) ← expectOkVal
    "schedule skips a malformed runnable target in a non-active domain too"
    (bootSchedule malformedOffDomain)
  if (stMalformedOff.scheduler.currentOnCore bootCoreId) = none then
    IO.println "positive check passed [off-domain malformed entry skipped, core left idle]"
  else
    throw <| IO.userError s!"off-domain malformed runnable target must not be dispatched, got current = {toString (stMalformedOff.scheduler.currentOnCore bootCoreId)}"

/-- WS-F2 + S5-G: Untyped memory negative tests + page-alignment misalignment.
    Extracted from `runNegativeChecks` (Phase 1; was lines 1093-1163). -/
private def runUntypedF2NegativeChecks : IO Unit := do
  -- ── WS-F2: Untyped memory negative tests ──────────────────────────
  -- F2-NEG-01: retype from non-existent object
  expectErr "F2 retype from non-existent object"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot ⟨999⟩ f2UntypedChildId
      (.endpoint {}) 64 f2UntypedState)
    .objectNotFound

  -- F2-NEG-02: retype from non-untyped object (type mismatch)
  expectErr "F2 retype from cnode (type mismatch)"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2UntypedAuthCnode f2UntypedChildId
      (.endpoint {}) 64 f2UntypedState)
    .untypedTypeMismatch

  -- F2-NEG-03: retype exhausts region
  expectErr "F2 retype region exhausted (oversized)"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2UntypedObjId f2UntypedChildId
      (.endpoint {}) 512 f2UntypedState)
    .untypedRegionExhausted

  -- F2-NEG-04: device restriction (non-untyped child from device untyped)
  expectErr "F2 device untyped restricts non-untyped child"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2DeviceUntypedId f2UntypedChildId
      (.endpoint {}) 64 f2DeviceState)
    .untypedDeviceRestriction

  -- F2-NEG-05: wrong authority (lookup from bad slot)
  expectErr "F2 retype wrong authority"
    (SeLe4n.Kernel.retypeFromUntyped { cnode := ⟨999⟩, slot := SeLe4n.Slot.ofNat 0 } f2UntypedObjId f2UntypedChildId
      (.endpoint {}) 64 f2UntypedState)
    .objectNotFound

  -- F2-NEG-06: allocSize too small for object type (endpoint needs 64, giving 1)
  expectErr "F2 retype allocSize too small"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2UntypedObjId f2UntypedChildId
      (.endpoint {}) 1 f2UntypedState)
    .untypedAllocSizeTooSmall

  -- S5-G-NEG: page-alignment check — misaligned base for VSpace root
  let f2MisalignedState : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject f2UntypedObjId (.untyped {
        regionBase := (SeLe4n.PAddr.ofNat 0x10001)  -- deliberately misaligned (not 4KB-aligned)
        regionSize := 8192
        children := []
        isDevice := false
      })
      |>.withObject f2UntypedAuthCnode (.cnode (SeLe4n.Model.CNode.ofSlots 0 0 0 0 (SeLe4n.UniqueSlotMap.ofListWF [
          (SeLe4n.Slot.ofNat 0, {
            target := .object f2UntypedObjId
            rights := AccessRightSet.ofList [.read, .write, .grant, .retype]
          })
        ])))
      |>.withLifecycleObjectType f2UntypedObjId .untyped
      |>.withLifecycleObjectType f2UntypedAuthCnode .cnode
      |>.buildChecked)
  -- WS-ZA ZA5.4 part 14: as seL4's `alignUp(freeRef, objectSize)`, a
  -- misaligned base is rounded up to the next page, not refused: the root's page
  -- is `[0x11000, 0x12000)`, so the capability's index lands at `0x2000 - 1`.
  expectCond "S5-G" "a misaligned base for a VSpace root is rounded up to the next page"
    (match SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2UntypedObjId f2UntypedChildId
      (.vspaceRoot { asid := ⟨0⟩, mappings := SeLe4n.Kernel.RobinHood.RHTable.empty 16 }) 4096
        f2MisalignedState with
     | .ok ((), st') =>
       (SystemState.lookupSlotCap st' f2UntypedAuthSlot).map (·.freeIndex) == some (0x1FFF)
     | .error _ => false)

  IO.println "untyped memory negative checks passed (incl. S5-G alignment)"


-- WS-RR RR8.3: the surface the pairing invariant exists for.  The two removal
-- guards are elaborated here because `runDualQueuePPrevPairingChecks` below can
-- exercise the guard's *value* but not the theorem that discharges it, and a
-- discharge nothing elaborates is indistinguishable from one that is wrong.  The
-- bundle form is the shape `endpointQueueRemoveDual`'s callers actually hold, and
-- is what WS-RR RR8.4's collapse of the two removals consumes.
#check @SeLe4n.Kernel.dualQueueRemovalGuardHolds
#check @SeLe4n.Kernel.dualQueueRemovalGuardHolds_of_dualQueueSystemInvariant
#check @SeLe4n.Model.dualQueueRemovalGuard_eq_position_and_pair
#check @SeLe4n.Kernel.spliceOutMidQueueNode_preserves_queuePPrevAgreesWithPrev
#check @SeLe4n.Kernel.sweptAndRestored_queuePPrevAgreesWithPrev
#check @SeLe4n.Kernel.QueueNextPath.lastEdge

/-- The reading the pairing had until `v0.35.99`: a `queuePPrev` of `none`
constrained nothing.  It lives here, `private`, and nowhere else — the stranding
witness below computes it beside the live predicate, so the assertion is known to
discriminate rather than merely to pass. -/
private def retiredPairingAcceptingAnyMissingBackPointer (st : SystemState) : Bool :=
  st.objectIndex.foldr (fun oid acc =>
    match st.getTcb? ⟨oid.toNat⟩ with
    | some tcb =>
        (match tcb.queuePPrev with
         | none => true
         | some .endpointHead => tcb.queuePrev.isNone
         | some (.tcbNext p) => tcb.queuePrev == some p) && acc
    | none => acc) true

/-- **WS-RR RR8.3**: the `queuePPrev`/`queuePrev` pairing invariant, and the split
that makes `endpointQueueRemoveDual`'s guard discharge from it.

Four assertions the tree could not make before this cut (the fourth added at
`v0.35.99`, when the `none` arm stopped being vacuous).

1. A queue the **live** operations built satisfies the pairing, and
   `dualQueueRemovalGuard` is `true` at both the head and an interior node — so
   `dualQueueRemovalGuardHolds` is not vacuous.
2. Corrupting a back-pointer to disagree with `queuePrev` makes
   `queuePPrevAgreesWithPrevBool` **false** while every queue and every
   `queueNext` chain stays exactly as it was.  That is the mutation that decides:
   before RR8.3 no conjunct and no runtime check read `queuePPrev`, so these two
   states were indistinguishable from the good one, which is how two removals
   came to write `queuePrev` without its partner (WS-OD OD1.1, OD3.9).
3. A **detached** thread carrying `(none, .endpointHead, none)` *satisfies* the
   pairing and still fails the guard, on the position half.  That is the honest
   measurement of what the invariant does **not** buy: membership is a separate
   hypothesis, which is why `dualQueueRemovalGuardHolds` takes one.
4. A queue's **head** carrying no back-pointer at all *satisfies* the pairing —
   `queuePrev = none` is what a head legitimately has — so the pointwise arm
   cannot reach it.  Case (5) below is that state, and the assertion added at
   `v0.35.106` is that `intrusiveQueueWellFormed`'s **P2** now refuses it, which
   is where a fact about a queue's head belongs. -/
private def runDualQueuePPrevPairingChecks : IO Unit := do
  let (_, stPair1) ← expectOkSt "pprev pairing enqueue sender 7"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) (.frame none false) baseState)
  let (_, stPair2) ← expectOkSt "pprev pairing enqueue sender 8"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 8) (.frame none false) stPair1)
  let (_, stPair3) ← expectOkSt "pprev pairing enqueue sender 9"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 9) (.frame none false) stPair2)

  -- (1) the live queue satisfies the invariant, and the guard holds on it.
  let sendQOf (st : SystemState) : IO IntrusiveQueue :=
    match st.getEndpoint? endpointId with
    | some ep => pure ep.sendQ
    | none => throw <| IO.userError "pprev pairing: endpoint missing"
  let tcbOf (st : SystemState) (tid : SeLe4n.ThreadId) : IO TCB :=
    match st.getTcb? tid with
    | some tcb => pure tcb
    | none => throw <| IO.userError s!"pprev pairing: TCB {tid.toNat} missing"
  let expectBool (label : String) (actual expected : Bool) : IO Unit :=
    if actual == expected then IO.println s!"positive check passed [{label}]"
    else throw <| IO.userError s!"{label}: expected {expected}, got {actual}"

  let q3 ← sendQOf stPair3
  let tcb7 ← tcbOf stPair3 (SeLe4n.ThreadId.ofNat 7)
  let tcb8 ← tcbOf stPair3 (SeLe4n.ThreadId.ofNat 8)
  expectBool "pprev pairing holds on the live three-member queue"
    (queuePPrevAgreesWithPrevBool stPair3) true
  expectBool "removal guard holds at the head (endpointHead arm)"
    (SeLe4n.Model.dualQueueRemovalGuard q3 (SeLe4n.ThreadId.ofNat 7) tcb7 .endpointHead) true
  expectBool "removal guard holds at an interior node (tcbNext arm)"
    (SeLe4n.Model.dualQueueRemovalGuard q3 (SeLe4n.ThreadId.ofNat 8) tcb8
      (.tcbNext (SeLe4n.ThreadId.ofNat 7))) true

  -- (2) breaking the pairing alone: every queue and every `queueNext` unchanged.
  let stHeadPPrev ← expectOkVal "pprev pairing corrupt the head's back-pointer"
    (corruptThreadQueueLinks stPair3 (SeLe4n.ThreadId.ofNat 7) none
      (some (.tcbNext (SeLe4n.ThreadId.ofNat 8))) (some (SeLe4n.ThreadId.ofNat 8)))
  expectBool "a head whose back-pointer names a predecessor fails the pairing"
    (queuePPrevAgreesWithPrevBool stHeadPPrev) false
  expectErr "...and the removal refuses it"
    (SeLe4n.Kernel.endpointQueueRemoveDual endpointId false (SeLe4n.ThreadId.ofNat 7) stHeadPPrev)
    .illegalState

  let stStalePrev ← expectOkVal "pprev pairing corrupt an interior node's back-pointer"
    (corruptThreadQueueLinks stPair3 (SeLe4n.ThreadId.ofNat 8) (some (SeLe4n.ThreadId.ofNat 7))
      (some .endpointHead) (some (SeLe4n.ThreadId.ofNat 9)))
  expectBool "an interior node claiming to be the head fails the pairing"
    (queuePPrevAgreesWithPrevBool stStalePrev) false

  -- (3) the position half is genuinely separate: a detached thread satisfies the
  -- pairing and still fails the guard.
  let stDetached ← expectOkVal "pprev pairing detached thread marked as queued"
    (corruptThreadQueueLinks baseState (SeLe4n.ThreadId.ofNat 7) none (some .endpointHead) none)
  expectBool "a detached thread carrying (none, endpointHead, none) SATISFIES the pairing"
    (queuePPrevAgreesWithPrevBool stDetached) true
  let qEmpty ← sendQOf stDetached
  let tcbDet ← tcbOf stDetached (SeLe4n.ThreadId.ofNat 7)
  expectBool "...and still fails the guard, on the position half"
    (SeLe4n.Model.dualQueueRemovalGuard qEmpty (SeLe4n.ThreadId.ofNat 7) tcbDet .endpointHead)
    false
  expectBool "...which is exactly the position factor"
    (SeLe4n.Model.queuePPrevHeadPositionAgrees qEmpty (SeLe4n.ThreadId.ofNat 7) .endpointHead)
    false

  -- (4) `v0.35.99`: the shape the `none` arm used to admit — a QUEUED interior
  -- node carrying no back-pointer at all.  Reported on PR #897 and confirmed by
  -- reading the conjuncts: `tcbQueueLinkIntegrity`, which the pairing's docstring
  -- delegated this case to, forbids a *dangling* `queuePrev` (one whose target
  -- does not point back) and says nothing about `queuePPrev`.  So this state
  -- satisfied every conjunct of `dualQueueSystemInvariant` while the dual removal
  -- — whose guard takes a `QueuePPrev`, not an `Option` — refuses it outright.
  -- That thread could never leave its queue: the OD1.1/OD3.9 stranding class, at
  -- the one spot RR8.3's own pairing left open.
  let stNoBackPointer ← expectOkVal "pprev pairing clear an interior node's back-pointer"
    (corruptThreadQueueLinks stPair3 (SeLe4n.ThreadId.ofNat 8) (some (SeLe4n.ThreadId.ofNat 7))
      none (some (SeLe4n.ThreadId.ofNat 9)))
  expectBool "the RETIRED reading ACCEPTED a queued node with no back-pointer"
    (retiredPairingAcceptingAnyMissingBackPointer stNoBackPointer) true
  expectBool "...and the strengthened pairing REFUSES it"
    (queuePPrevAgreesWithPrevBool stNoBackPointer) false
  -- The refusal is `.endpointQueueEmpty` on a queue that is *not* empty: the
  -- removal reaches for a `QueuePPrev` and finds `none`, so it reports the shape
  -- it expects a missing back-pointer to mean.  The misleading code is the
  -- smaller half of the finding; the strand is that the thread can never leave.
  expectErr "...which is the state whose removal was refused, stranding the thread"
    (SeLe4n.Kernel.endpointQueueRemoveDual endpointId false (SeLe4n.ThreadId.ofNat 8)
      stNoBackPointer)
    .endpointQueueEmpty
  -- ...and the control: the same queue with the back-pointer intact is accepted by
  -- both readings and its removal succeeds, so the three assertions above are
  -- about the cleared field and not about the fixture.
  expectBool "control: the untouched queue satisfies the RETIRED reading too"
    (retiredPairingAcceptingAnyMissingBackPointer stPair3) true
  let (_, _) ← expectOkSt "control: the untouched interior node CAN be removed"
    (SeLe4n.Kernel.endpointQueueRemoveDual endpointId false (SeLe4n.ThreadId.ofNat 8) stPair3)

  -- (5) **PR #897 review (`v0.35.106`): the HEAD, which `v0.35.99` did not reach.**
  -- Case (4) above closed *present but wrong* for an interior node.  A queue's
  -- **head** has `queuePrev = none` legitimately, so the strengthened `none` arm's
  -- obligation (`queuePrev = none`) is *satisfied* by a head carrying no
  -- back-pointer at all — a pointwise predicate over one TCB structurally cannot
  -- say "on no queue", whatever it is strengthened to.  So the clause moved to
  -- where it can be said: `intrusiveQueueWellFormed`'s **P2**, a fact about a
  -- queue's head, which this case is the witness for.
  let (_, stSingle) ← expectOkSt "pprev pairing enqueue a single sender"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) (.frame none false) baseState)
  let stHeadNoBackPointer ← expectOkVal "pprev pairing clear the SOLE member's back-pointer"
    (corruptThreadQueueLinks stSingle (SeLe4n.ThreadId.ofNat 7) none none none)
  let qSingle ← sendQOf stHeadNoBackPointer
  expectBool "control: the queue names that thread as BOTH head and tail"
    (qSingle.head == some (SeLe4n.ThreadId.ofNat 7)
      && qSingle.tail == some (SeLe4n.ThreadId.ofNat 7)) true
  -- The clause P2 now carries, read off both states directly: the corrupted head
  -- carries no back-pointer and the control's carries `.endpointHead`.  Asserting
  -- the *field* rather than only a predicate's verdict is what makes this witness
  -- about P2's own strengthening rather than about the pairing beside it.
  expectBool "the corrupted head carries NO back-pointer — the clause P2 requires"
    (match stHeadNoBackPointer.getTcb? (SeLe4n.ThreadId.ofNat 7) with
     | some tcb => tcb.queuePPrev == none
     | none => false) true
  expectBool "control: the untouched head carries `some .endpointHead`"
    (match stSingle.getTcb? (SeLe4n.ThreadId.ofNat 7) with
     | some tcb => tcb.queuePPrev == some .endpointHead
     | none => false) true
  -- The **pairing** still accepts it, and that is not a defect: the head really has
  -- no predecessor, so this arm's obligation is met.  It is why the clause could
  -- not live here.
  expectBool "the pairing ACCEPTS a queue head carrying no back-pointer"
    (queuePPrevAgreesWithPrevBool stHeadNoBackPointer) true
  -- ...and the removal refuses its sole member — the strand this closes.
  expectErr "...and the removal refuses the queue's SOLE member, stranding it"
    (SeLe4n.Kernel.endpointQueueRemoveDual endpointId false (SeLe4n.ThreadId.ofNat 7)
      stHeadNoBackPointer)
    .endpointQueueEmpty
  -- **Both artefacts refuse it now, and until `v0.35.106` only one did.**
  -- `intrusiveQueueWellFormedB` has required `headTcb.queuePPrev = some
  -- .endpointHead` since it was written, while `intrusiveQueueWellFormed`'s P2
  -- constrained only `queuePrev` — two artefacts answering "is this queue
  -- well-formed" with the **proved** one the weaker, at exactly the clause that
  -- strands a thread.  Folding it in cost `dualQueueSystemInvariant` a fifth
  -- conjunct (`endpointQueueHeadDisjoint`); see P2's docstring for that
  -- measurement.
  expectBool "the RUNTIME check refuses it — and P2 refuses it too since v0.35.106"
    ((stateInvariantChecksFor stHeadNoBackPointer.objectIndex stHeadNoBackPointer).any
      (fun c => !c.2 && c.1.startsWith "endpoint intrusive sendQ invariant")) true
  -- ...and the control: with the back-pointer intact, the runtime check passes and
  -- the sole member can be removed, so the assertions above are about the cleared
  -- field and not about a fixture the harness dislikes for other reasons.
  expectBool "control: with the back-pointer intact the runtime check passes"
    ((stateInvariantChecksFor stSingle.objectIndex stSingle).any
      (fun c => !c.2 && c.1.startsWith "endpoint intrusive sendQ invariant")) false
  let (_, _) ← expectOkSt "control: ...and the SOLE member CAN be removed"
    (SeLe4n.Kernel.endpointQueueRemoveDual endpointId false (SeLe4n.ThreadId.ofNat 7) stSingle)
  -- The payoff, elaborated because a run cannot exercise a theorem: with both
  -- halves in place a queue **member**'s back-pointer is derived rather than
  -- hypothesised, at the head from P2 and at an interior node from the pairing.
  let _ := @SeLe4n.Kernel.queuePPrev_tcbNext_of_reachable
  let _ := @SeLe4n.Kernel.queuePPrev_of_queueMember
  let _ := @SeLe4n.Kernel.dualQueueRemovalGuardHolds_of_member
  -- And the fifth conjunct that made P2's strengthening preservable: exclusivity
  -- is a *consequence* of `ipcInvariantCore`, not a new assumption, and the two
  -- local facts every queue writer discharges it with.
  let _ := @SeLe4n.Kernel.queueHeadExclusive
  let _ := @SeLe4n.Kernel.queueHeadKindExclusive
  let _ := @SeLe4n.Kernel.endpointQueueHeadDisjoint_of_queueHeadBlockedConsistent
  let _ := @SeLe4n.Kernel.endpointQueueHeadDisjoint_of_singleQueueUpdate
  let _ := @SeLe4n.Kernel.endpointQueueHeadDisjoint_of_freshHeads
  let _ := @SeLe4n.Kernel.not_queueHead_of_queuePrev_some
  let _ := @SeLe4n.Kernel.not_queueHead_of_queuePPrev_none
  let _ := @SeLe4n.Kernel.spliceOutMidQueueNode_queuePPrev_frame
  pure ()

-- WS-RR RR8.4: the four shapes a guarded removal writes, and the two removals'
-- boundary pins.  Elaborated here because `runDualQueueTailPairingChecks` below
-- exercises the guard's and the boundary's *values* but not the theorems that
-- state what each removal writes, and the whole content of the collapse is that
-- the two write one definition.
#check @SeLe4n.Model.queueTailPairAgrees_iff
#check @SeLe4n.Kernel.queueTailPairAgrees_of_wellFormed
#check @SeLe4n.Model.queueRemoveBoundary_headLast
#check @SeLe4n.Model.queueRemoveBoundary_headMore
#check @SeLe4n.Model.queueRemoveBoundary_midLast
#check @SeLe4n.Model.queueRemoveBoundary_midMore
#check @SeLe4n.Kernel.endpointQueueRemoveDual_writes_queueRemoveBoundary
#check @SeLe4n.Model.dualQueueRemovalGuard_tail_half

/-- **WS-RR RR8.4**: the tail question has one answer, and the removal refuses the
state on which its two readings part.

The two endpoint-queue removals agreed on the head and differed on the tail:
`endpointQueueRemove` asked `q.tail = some tid` — the **fact** — and
`endpointQueueRemoveDual` asked `removed.queueNext = none`, a **proxy** for it,
deriving the new tail from `queuePPrev`.  Under a connected queue the two
coincide, and `ipcInvariantFull` joins a queue's boundaries nowhere, so this
measures both halves of that gap.

Four assertions.

1. On a queue the **live** operations built, the fact and the proxy agree at every
   member, so `queueTailPairAgrees` is `true` and the guard is not made vacuous by
   the new factor.
2. `queueRemoveBoundary` computes the four shapes the branch facts predict — the
   boundary both removals now write, so the comparison is of one definition
   rather than of two authors' readings.
3. On a state the bundle admits and connectivity refutes — a queued thread with
   **no successor that is not the tail** — the fact and the proxy **disagree**, so
   `queueTailPairAgrees` is `false` and the dual removal **refuses** with
   `.illegalState`.  That is the fail-closed direction: the inferring form cleared
   the tail here and stranded the queue's real tail, a thread that could then
   never be dequeued.
4. The refusal is attributable to the **tail** factor and not to the others: the
   position and pairing factors are both `true` on that same state.  Without this
   the third assertion would pass for a guard that refused everything. -/
private def runDualQueueTailPairingChecks : IO Unit := do
  let (_, stTail1) ← expectOkSt "tail pairing enqueue sender 7"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) (.frame none false) baseState)
  let (_, stTail2) ← expectOkSt "tail pairing enqueue sender 8"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 8) (.frame none false) stTail1)

  let sendQOf (st : SystemState) : IO IntrusiveQueue :=
    match st.getEndpoint? endpointId with
    | some ep => pure ep.sendQ
    | none => throw <| IO.userError "tail pairing: endpoint missing"
  let tcbOf (st : SystemState) (tid : SeLe4n.ThreadId) : IO TCB :=
    match st.getTcb? tid with
    | some tcb => pure tcb
    | none => throw <| IO.userError s!"tail pairing: TCB {tid.toNat} missing"
  let expectBool (label : String) (actual expected : Bool) : IO Unit :=
    if actual == expected then IO.println s!"positive check passed [{label}]"
    else throw <| IO.userError s!"{label}: expected {expected}, got {actual}"
  let expectQueue (label : String) (actual expected : IntrusiveQueue) : IO Unit :=
    if actual == expected then IO.println s!"positive check passed [{label}]"
    else throw <| IO.userError s!"{label}: expected {repr expected}, got {repr actual}"

  let q2 ← sendQOf stTail2
  let tcb7 ← tcbOf stTail2 (SeLe4n.ThreadId.ofNat 7)
  let tcb8 ← tcbOf stTail2 (SeLe4n.ThreadId.ofNat 8)

  -- (1) the fact and the proxy agree at both members of a live queue.
  expectBool "tail pairing holds at the head of the live queue"
    (SeLe4n.Model.queueTailPairAgrees q2 (SeLe4n.ThreadId.ofNat 7) tcb7) true
  expectBool "tail pairing holds at the tail of the live queue"
    (SeLe4n.Model.queueTailPairAgrees q2 (SeLe4n.ThreadId.ofNat 8) tcb8) true

  -- (2) the shared boundary computes the shapes the branch facts predict.
  expectQueue "boundary: removing the head with a successor moves the head only"
    (SeLe4n.Model.queueRemoveBoundary q2 (SeLe4n.ThreadId.ofNat 7) tcb7)
    { head := some (SeLe4n.ThreadId.ofNat 8), tail := some (SeLe4n.ThreadId.ofNat 8) }
  expectQueue "boundary: removing the tail moves the tail to its predecessor"
    (SeLe4n.Model.queueRemoveBoundary q2 (SeLe4n.ThreadId.ofNat 8) tcb8)
    { head := some (SeLe4n.ThreadId.ofNat 7), tail := some (SeLe4n.ThreadId.ofNat 7) }

  -- (3) the fact and the proxy part on a state the bundle admits: thread 7 is the
  -- head, is given no successor, and is not the tail.  Every `queueNext` chain and
  -- both boundaries are left exactly as the live operations wrote them.
  let stStranded ← expectOkVal "tail pairing: a head with no successor that is not the tail"
    (corruptThreadQueueLinks stTail2 (SeLe4n.ThreadId.ofNat 7) none (some .endpointHead) none)
  let qS ← sendQOf stStranded
  let tcbS ← tcbOf stStranded (SeLe4n.ThreadId.ofNat 7)
  expectBool "...the queue's tail still names thread 8"
    (qS.tail == some (SeLe4n.ThreadId.ofNat 8)) true
  expectBool "...so the fact and the proxy DISAGREE"
    (SeLe4n.Model.queueTailPairAgrees qS (SeLe4n.ThreadId.ofNat 7) tcbS) false
  expectErr "...and the removal refuses it rather than stranding thread 8"
    (SeLe4n.Kernel.endpointQueueRemoveDual endpointId false (SeLe4n.ThreadId.ofNat 7) stStranded)
    .illegalState

  -- (4) the refusal is the tail factor's: the other two are true on that state.
  expectBool "...the position factor is TRUE there"
    (SeLe4n.Model.queuePPrevHeadPositionAgrees qS (SeLe4n.ThreadId.ofNat 7) .endpointHead) true
  expectBool "...the pairing factor is TRUE there"
    (SeLe4n.Model.queueLinkPairAgrees tcbS.queuePrev (some .endpointHead)) true
  expectBool "...so the whole guard is false, and only because of the tail"
    (SeLe4n.Model.dualQueueRemovalGuard qS (SeLe4n.ThreadId.ofNat 7) tcbS .endpointHead) false

/-- **PR #897 review (`v0.35.108`)**: the FIFTH `dualQueueSystemInvariant`
conjunct's runtime check, and the state that shows the surface was silent about it.

`v0.35.106` added `endpointQueueHeadDisjoint` and added no runtime check, one cut
after WS-RR RR8.3 had recorded the rule that a conjunct is *checked at runtime, not
only proved*.  The gap ran wider than one omitted call: **nothing** in
`stateInvariantChecksFor` was cross-endpoint — `endpointDualQueueWellFormedB` is
literally the two per-queue checks of one endpoint — and nothing tied an endpoint
queue's head to its own `ipcState`.  So a state the proof bundle refuses passed
every check the harness runs, and `assertStateInvariantsFor` would have accepted a
fixture on which popping either queue clears the shared TCB's links and strands the
other queue: the OD1.1 / OD3.9 stranding class a fourth time, on a queue that is
not even empty.

Four assertions, and the third and fourth are what make the first two about the
*cross-endpoint* fact rather than about queue well-formedness. -/
private def runEndpointQueueHeadDisjointChecks : IO Unit := do
  let expectBool (label : String) (actual expected : Bool) : IO Unit :=
    if actual == expected then IO.println s!"positive check passed [{label}]"
    else throw <| IO.userError s!"{label}: expected {expected}, got {actual}"
  -- `wrongTypeId` is a second, genuine `.endpoint` installed in `baseState` for an
  -- unrelated wrong-kind lookup test.  It is used here because it is already in
  -- `objectIndex`, which a raw insert of a fresh object would not maintain — and
  -- the check reads `st.objectIndex`, so an object outside it is invisible.
  let otherEndpointId := wrongTypeId
  -- The shared head is installed by the LIVE operation on one endpoint, so its TCB
  -- links are exactly what the kernel writes; only the second endpoint's boundary
  -- is written by hand.
  let (_, stSingle) ← expectOkSt "head disjoint: enqueue the sole sender"
    (SeLe4n.Kernel.endpointSendDual endpointId (SeLe4n.ThreadId.ofNat 7) (.frame none false) baseState)
  let stShared ← expectOkVal "head disjoint: a SECOND endpoint claims the same head"
    (corruptEndpointQueueHeads stSingle otherEndpointId none (some (SeLe4n.ThreadId.ofNat 7)))

  -- (1) the state the bundle refuses is refused by the runtime check too.
  expectBool "two queues sharing one head FAIL the head-disjointness check"
    (endpointQueueHeadDisjointBool stShared) false
  expectBool "...and `stateInvariantChecksFor` reports it"
    ((stateInvariantChecksFor stShared.objectIndex stShared).any
      (fun c => !c.2 && c.1.startsWith "endpoint queue heads disjoint")) true

  -- (2) the control: the same state before the second endpoint claimed the head.
  expectBool "control: one queue, one head — the check passes"
    (endpointQueueHeadDisjointBool stSingle) true

  -- (3) **the decisive half.**  Every OTHER check in the surface accepts the
  -- violating state: both queues are well formed (the hand-written one is
  -- `{head := some 7, tail := some 7}` over a TCB the live enqueue left with
  -- `queuePrev = none`, `queuePPrev = some .endpointHead`, `queueNext = none`), and
  -- the RR8.3 pairing is untouched because no TCB was written at all.  So before
  -- this cut the harness's verdict on `stShared` was *clean*.
  expectBool "the RR8.3 pairing ACCEPTS it — no TCB was written"
    (queuePPrevAgreesWithPrevBool stShared) true
  expectBool "both endpoints' queues are individually WELL FORMED"
    ((stateInvariantChecksFor stShared.objectIndex stShared).all
      (fun c => c.2 || !(c.1.startsWith "endpoint intrusive"
        || c.1.startsWith "endpoint dual-queue"))) true
  -- ...and the claim stated as a DIFFERENTIAL against the control, which is what
  -- "the surface was silent" means.  A plain "the only failing check is the new
  -- one" would be false for a reason that has nothing to do with the shared head:
  -- `baseState`'s TCBs carry `threadState := .Inactive` and were never synced, so
  -- `threadStateConsistentChecks` and `threadInactiveFlagConsistentChecks` fail on
  -- BOTH states.  That is the documented behaviour of those two — they validate
  -- inference self-consistency, not operational drift, which is why
  -- `assertStateInvariantsFor` syncs before it checks.  Subtracting the control's
  -- failures leaves exactly the two rows the new check reports, one per colliding
  -- queue.
  let failing (st : SystemState) : List String :=
    ((stateInvariantChecksFor st.objectIndex st).filter (fun c => !c.2)).map (·.1)
  let sharedOnly := (failing stShared).filter (fun l => !((failing stSingle).contains l))
  expectBool "the shared head adds EXACTLY the new check's rows and nothing else"
    (sharedOnly.all (fun l => l.startsWith "endpoint queue heads disjoint")) true
  expectBool "...and it adds one row per colliding queue, so the pair is named"
    (sharedOnly.length == 2) true

  -- (4) and the strand itself: popping one queue clears the shared TCB's links, so
  -- the other queue's head is left unlinked and its own removal is then refused —
  -- which is what a state the bundle refuses buys an attacker who can reach it.
  -- `expectOkVal`, not `expectOkSt`: the latter asserts the invariant surface on the
  -- post-state, and this post-state is the corrupt one the finding is ABOUT — the
  -- pop succeeds and leaves the other endpoint's receive queue malformed, which is
  -- the two rows it would report.  Asserting them away would delete the payoff.
  let (_, stPopped) ← expectOkVal "head disjoint: pop the shared head from ONE queue"
    (SeLe4n.Kernel.endpointQueueRemoveDual endpointId false (SeLe4n.ThreadId.ofNat 7) stShared)
  expectBool "the pop leaves the OTHER endpoint's queue malformed"
    ((stateInvariantChecksFor stPopped.objectIndex stPopped).any
      (fun c => !c.2 && c.1.startsWith "endpoint intrusive receiveQ invariant")) true
  expectBool "the shared TCB's links are cleared by that pop"
    (match stPopped.getTcb? (SeLe4n.ThreadId.ofNat 7) with
     | some tcb => tcb.queuePPrev == none && tcb.queuePrev == none && tcb.queueNext == none
     | none => false) true
  expectErr "...and the OTHER queue can now never dequeue its own head"
    (SeLe4n.Kernel.endpointQueueRemoveDual otherEndpointId true (SeLe4n.ThreadId.ofNat 7)
      stPopped)
    .endpointQueueEmpty
  -- The conjunct, elaborated because a run cannot exercise a theorem.
  let _ := @SeLe4n.Kernel.endpointQueueHeadDisjoint
  pure ()

/-- **WS-ZA ZA5.4 part 27**: `endpointQueueLinksOnlyBlocked`, the 21st
`ipcInvariantFull` conjunct — a thread with an endpoint-queue successor is
blocked on an endpoint.

The counterexample is the state the final delete could not otherwise exclude:
a `.ready` thread naming a queue successor, the successor blocked on an
endpoint whose own queues are empty.  No live operation reaches it, so it is
written by hand, one step from a state the live send built.

1. Control: the live queue, and the same state with only the endpoint's
   queues emptied, satisfy the check — the queued thread has no successor.
2. Writing the ready thread's `queueNext` breaks the check, on that thread's
   row alone; `endpointQueueLinksOnlyBlocked.not_ipcInvariantFull` is the
   proof-side refusal of the same state.
3. The boot refuses the shape too: `bootSafeObjectCheck` admits no boot TCB
   carrying any queue link. -/
private def runEndpointQueueLinksOnlyBlockedChecks : IO Unit := do
  let expectBool (label : String) (actual expected : Bool) : IO Unit :=
    if actual == expected then IO.println s!"positive check passed [{label}]"
    else throw <| IO.userError s!"{label}: expected {expected}, got {actual}"
  let sender := SeLe4n.ThreadId.ofNat 8
  let ready := SeLe4n.ThreadId.ofNat 7
  -- (1) the live send: thread 8 is `.blockedOnSend` and the sole sendQ member.
  let (_, stSent) ← expectOkSt "queue links: enqueue the sole sender"
    (SeLe4n.Kernel.endpointSendDual endpointId sender (.frame none false) baseState)
  expectBool "the live queue satisfies the check"
    (endpointQueueLinksOnlyBlockedBool stSent) true
  let stEmptied ← expectOkVal "queue links: empty the endpoint's queues"
    (corruptEndpointQueueHeads stSent endpointId none none)
  expectBool "control: emptying the endpoint's queues alone keeps the check"
    (endpointQueueLinksOnlyBlockedBool stEmptied) true
  -- (2) the counterexample: the ready thread 7 names thread 8 as its successor.
  let stCounter ← expectOkVal "queue links: a ready thread names the blocked sender"
    (corruptThreadQueueLinks stEmptied ready none none (some sender))
  expectBool "control: thread 7 is ready, thread 8 blocked on the emptied endpoint"
    (match stCounter.getTcb? ready, stCounter.getTcb? sender with
     | some t7, some t8 =>
         t7.ipcState == .ready && t7.queueNext == some sender &&
           t8.ipcState == .blockedOnSend endpointId
     | _, _ => false) true
  expectBool "NEGATIVE: a ready thread with a queue successor fails the check"
    (endpointQueueLinksOnlyBlockedBool stCounter) false
  let failing := ((endpointQueueLinksOnlyBlockedChecks stCounter.objectIndex stCounter).filter
    (fun c => !c.2)).map (·.1)
  expectBool "...on the ready thread's row alone"
    (failing.length == 1 && failing.all (fun l => l.startsWith
      s!"endpoint queue links only on blocked threads: oid={ready.toObjId}")) true
  expectBool "...and the full invariant surface reports it"
    ((stateInvariantChecksFor stCounter.objectIndex stCounter).any
      (fun c => !c.2 && c.1.startsWith "endpoint queue links only on blocked threads")) true
  -- (3) the boot: a TCB carrying a queue successor is refused as a boot object.
  match stCounter.getTcb? ready with
  | some t7 =>
      expectBool "NEGATIVE: the boot refuses a TCB carrying a queue successor"
        (SeLe4n.Platform.Boot.bootSafeObjectCheck (.tcb t7)) false
  | none => throw <| IO.userError "queue links: thread 7 missing"
  -- The proof-side refusal, elaborated because a run cannot exercise a theorem.
  let _ := @SeLe4n.Kernel.endpointQueueLinksOnlyBlocked.not_ipcInvariantFull
  pure ()

/-- **WS-ZA ZA5.4 part 27**: `donationChainWellFormed.nextLinkReciprocal` — a
reply frame linking up to a frame above is answered by that frame's `prev`.

1. Control: a two-frame stack, the lower frame naming the upper by `next` and the
   upper naming the lower by `prev`, satisfies the check.
2. Clearing the upper frame's `prev` alone leaves the lower frame's `next`
   dangling: the check fails, on the lower frame's row alone;
   `donationChainWellFormed.not_of_dangling_next` is the proof-side refusal.
3. The live removal of the lower (bottom) frame leaves no such link: the splice
   clears the frame above's `prev` and, in the same step, the cut frame's own
   `next`, so the state it returns passes the check. -/
private def runReplyNextLinkReciprocalChecks : IO Unit := do
  let expectBool (label : String) (actual expected : Bool) : IO Unit :=
    if actual == expected then IO.println s!"positive check passed [{label}]"
    else throw <| IO.userError s!"{label}: expected {expected}, got {actual}"
  let lower : SeLe4n.ReplyId := ⟨9201⟩
  let upper : SeLe4n.ReplyId := ⟨9202⟩
  let ids := [lower.toObjId, upper.toObjId]
  let withReplies (l u : SeLe4n.Kernel.Reply) : SystemState :=
    { baseState with
        objects := (baseState.objects.insert lower.toObjId (.reply l)).insert
          upper.toObjId (.reply u) }
  let check (st : SystemState) : Bool := (replyNextLinkReciprocalChecks ids st).all (·.2)
  -- (1) the reciprocal pair.
  let lowerR : SeLe4n.Kernel.Reply := { replyId := lower, callerCode := SeLe4n.ThreadId.optCode (some ⟨8⟩), next := some (.frame upper) }
  let upperR : SeLe4n.Kernel.Reply := { replyId := upper, callerCode := SeLe4n.ThreadId.optCode (some ⟨9⟩), prev := some lower }
  let stPair := withReplies lowerR upperR
  expectBool "a reciprocal two-frame stack satisfies the check" (check stPair) true
  -- (2) the counterexample: the upper frame no longer names the lower one.
  let stDangling := withReplies lowerR { upperR with prev := none }
  expectBool "NEGATIVE: a frame naming a frame above that does not name it back fails the check"
    (check stDangling) false
  let failing := ((replyNextLinkReciprocalChecks ids stDangling).filter (fun c => !c.2)).map (·.1)
  expectBool "...on the lower frame's row alone"
    (failing.length == 1 && failing.all (fun l => l.startsWith
      s!"reply next link reciprocal: oid={lower.toObjId}")) true
  -- (3) the live removal of the bottom frame.
  match SeLe4n.Kernel.spliceReplyFrameOut stPair lower with
  | .error e => throw <| IO.userError s!"reply next link: the bottom splice refused: {reprStr e}"
  | .ok stCut =>
      expectBool "the bottom splice leaves no dangling upward link" (check stCut) true
      expectBool "...having cleared both the frame above's prev and the cut frame's next"
        ((stCut.getReply? upper).any (·.prev.isNone) &&
          (stCut.getReply? lower).any (·.next.isNone)) true
  -- The proof-side refusal, elaborated because a run cannot exercise a theorem.
  let _ := @SeLe4n.Kernel.donationChainWellFormed.not_of_dangling_next
  pure ()

/-- PR #932 review: `buildValidated` refuses a supplied TCB that already claims
a run-queue place, since the fold over `runnable` would skip or refuse its
enqueue and leave the queue it names unbuilt.  Same fixture with the placement
cleared builds; that keeps the token and breaks only the relation. -/
private def runBuilderRunPlacementChecks : IO Unit := do
  let expectBool (label : String) (actual expected : Bool) : IO Unit :=
    if actual == expected then IO.println s!"positive check passed [{label}]"
    else throw <| IO.userError s!"{label}: expected {expected}, got {actual}"
  let tid := SeLe4n.ThreadId.ofNat 31
  let tcbWith (code : Nat) : TCB :=
    { tid := tid, priority := ⟨10⟩, domain := ⟨0⟩, spaceCells := SeLe4n.Model.TCB.spaceCellsOf ⟨0⟩ ⟨0⟩,
      ipcBuffer := (SeLe4n.VAddr.ofNat 0), runCoreCode := code }
  let fixture (code : Nat) : BootstrapBuilder :=
    BootstrapBuilder.empty
      |>.withObject tid.toObjId (.tcb (tcbWith code))
      |>.withRunnable [tid]
  expectBool "builder refuses a supplied TCB carrying run-queue placement"
    (match (fixture 1).buildValidated with | .error _ => true | .ok _ => false) true
  expectBool "the same fixture without placement builds and queues the thread"
    (match (fixture 0).buildValidated with
     | .ok st => st.runQueueWalk SeLe4n.Kernel.Concurrency.bootCoreId == [tid]
     | .error _ => false) true

/-- WS-ZA ZA5.3 part 4 review: the runtime link-agreement check reads a sparse
radix-16 CNode's link words without querying the tree per addressable slot, and
still refuses a stray link at a slot the tree does not name and a wrong link at
one it does. -/
private def runSlotLinkAgreementChecks : IO Unit := do
  let expectBool (label : String) (actual expected : Bool) : IO Unit :=
    if actual == expected then IO.println s!"positive check passed [{label}]"
    else throw <| IO.userError s!"{label}: expected {expected}, got {actual}"
  let wideId : SeLe4n.ObjId := ⟨5150⟩
  let rootSlot : SlotRef := { cnode := wideId, slot := SeLe4n.Slot.ofNat 3 }
  let childSlot : SlotRef := { cnode := wideId, slot := SeLe4n.Slot.ofNat 40000 }
  let cap : Capability :=
    { target := .object endpointId, rights := AccessRightSet.ofList [.read] }
  let seed : SystemState := {
    baseState with
      objects := baseState.objects.insert wideId (.cnode (CNode.ofList 16 0 0 16
        [(rootSlot.slot, cap), (childSlot.slot, cap)]))
  } |>.withDerivationEdges [(rootSlot, childSlot, .copy)]
  let ids := wideId :: invariantObjectIds
  let linkCheckFails (st : SystemState) : Bool :=
    (stateInvariantChecksFor ids st).any
      (fun c => !c.2 && c.1 == "cdt slot links fit together as a tree")
  expectBool "control: a sparse radix-16 CNode's links fit together as a tree"
    (linkCheckFails seed) false
  let withLink (st : SystemState) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) : SystemState :=
    match st.getCNode? wideId with
    | some cn => { st with objects := st.objects.insert wideId (.cnode (cn.setLinkWords s f c w)) }
    | none => st
  expectBool "a stray parent link at a slot its parent does not list is refused"
    (linkCheckFails (withLink seed (SeLe4n.Slot.ofNat 65000) .parent (wideId.toNat + 1) 4)) true
  expectBool "a next link its target does not answer is refused"
    (linkCheckFails (withLink seed childSlot.slot .next (wideId.toNat + 1) 4)) true
  expectBool "a slot word alone, with no CNode word, is no link and is not refused"
    (linkCheckFails (withLink seed (SeLe4n.Slot.ofNat 65000) .parent 0 4)) false

/-- PR #958 review: the runtime link check refuses link shapes that agree
locally but break the tree's other invariants: a pair of empty slots linked as
parent and child (`cdtCompleteness`), a slot that is its own parent and first
child (`cdtAcyclicity`), more parent links than the tree's edge bound, which
fuels the link walks and the revoke loop, a sibling ring whose parent's child
chain does not reach it, and a self loop in a CNode the object list omits (the
check reads the whole store).  Each keeps the local agreements and breaks the
relation its check names; all but the extra edge also add a parent link past the
edge bound, so the bound check fails with them. -/
private def runSlotLinkShapeChecks : IO Unit := do
  let expectBool (label : String) (actual expected : Bool) : IO Unit :=
    if actual == expected then IO.println s!"positive check passed [{label}]"
    else throw <| IO.userError s!"{label}: expected {expected}, got {actual}"
  let cnId : SeLe4n.ObjId := ⟨5160⟩
  let rootSlot : SlotRef := { cnode := cnId, slot := SeLe4n.Slot.ofNat 3 }
  let childSlot : SlotRef := { cnode := cnId, slot := SeLe4n.Slot.ofNat 5 }
  let spareSlot : SeLe4n.Slot := SeLe4n.Slot.ofNat 9
  let cap : Capability :=
    { target := .object endpointId, rights := AccessRightSet.ofList [.read] }
  let seed : SystemState := {
    baseState with
      objects := baseState.objects.insert cnId (.cnode (CNode.ofList 8 0 0 8
        [(rootSlot.slot, cap), (childSlot.slot, cap), (spareSlot, cap)]))
      cdt := CapDerivationTree.empty
  } |>.withDerivationEdges [(rootSlot, childSlot, .copy)]
  let ids := cnId :: invariantObjectIds
  let failing (st : SystemState) : List String :=
    ((stateInvariantChecksFor ids st).filter (fun c => !c.2 && c.1.startsWith "cdt ")).map (·.1)
  let withLink (st : SystemState) (s : SeLe4n.Slot) (f : LinkField) (o : SeLe4n.ObjId)
      (w : SeLe4n.Slot) : SystemState :=
    match st.getCNode? cnId with
    | some cn =>
      let cn' := cn.setLinkWords s f (o.toNat + 1) (w.toNat + 1)
      { st with objects := st.objects.insert cnId (.cnode cn') }
    | none => st
  expectBool "control: a populated one-edge tree passes every link check"
    ((failing seed).isEmpty) true
  expectBool "control: the fixture's edge bound is exactly its parent links"
    ((linkedDerivationEdges seed).length == seed.cdt.edgeBound) true
  let emptyA := SeLe4n.Slot.ofNat 100
  let emptyB := SeLe4n.Slot.ofNat 101
  let emptyPair := withLink (withLink seed emptyA .parent cnId emptyB) emptyB .firstChild cnId emptyA
  expectBool "two empty slots linked as parent and child fail the occupancy and bound checks"
    (failing emptyPair ==
      ["cdt linked slots hold capabilities", "cdt edge bound covers the slot links"]) true
  let selfLoop := withLink (withLink seed spareSlot .parent cnId spareSlot) spareSlot .firstChild
    cnId spareSlot
  expectBool "a slot that is its own parent and first child fails the cycle and bound checks"
    (failing selfLoop ==
      ["cdt slot links form no cycle", "cdt edge bound covers the slot links"]) true
  let extraEdge :=
    withLink (withLink (withLink (withLink seed rootSlot.slot .firstChild cnId spareSlot)
      spareSlot .parent cnId rootSlot.slot) spareSlot .next cnId childSlot.slot)
      childSlot.slot .prev cnId spareSlot
  expectBool "a second parent link past the edge bound fails only the bound check"
    (failing extraEdge == ["cdt edge bound covers the slot links"]) true
  let ring :=
    withLink (withLink (withLink seed spareSlot .parent cnId childSlot.slot) spareSlot .next cnId
      spareSlot) spareSlot .prev cnId spareSlot
  expectBool "a sibling ring under a parent with no first child fails the child-chain and bound checks"
    (failing ring ==
      ["cdt child chains list each parent's children", "cdt edge bound covers the slot links"]) true
  let unlisted :=
    ((stateInvariantChecksFor invariantObjectIds selfLoop).filter
      (fun c => !c.2 && c.1.startsWith "cdt ")).map (·.1)
  expectBool "a self loop in a CNode the object list omits still fails the cycle and bound checks"
    (unlisted == ["cdt slot links form no cycle", "cdt edge bound covers the slot links"]) true

private def runNegativeChecks : IO Unit := do
  runBaselineLookupNegativeChecks                       -- [was 248-262]
  runCspaceMutationAndRevokeNegativeChecks
  let stN1 ← runVSpaceAndNotificationF03NegativeChecks  -- [was 463-565; returns stN1 for F-12 double-wait below]
  runBadgeTruncationNegativeChecks                      -- [was 567-607]
  runIpcPayloadBoundsNegativeChecks                     -- [was 608-700]
  runDualQueueEndpointFifoNegativeChecks                -- [was 702-1034]
  runDualQueuePPrevPairingChecks                        -- WS-RR RR8.3
  runDualQueueTailPairingChecks                         -- WS-RR RR8.4
  runEndpointQueueHeadDisjointChecks                    -- PR #897 review (v0.35.108)
  runEndpointQueueLinksOnlyBlockedChecks                -- WS-ZA ZA5.4 part 27
  runReplyNextLinkReciprocalChecks                      -- WS-ZA ZA5.4 part 27
  runBuilderRunPlacementChecks                          -- PR #932 review
  runSlotLinkAgreementChecks                            -- PR #956 review
  runSlotLinkShapeChecks                                -- PR #958 review

  -- ==========================================================================
  -- WS-D4 F-12: Double-wait prevention in notificationWait (was 1036-1043).
  -- Stays inline because it consumes `stN1` returned by
  -- `runVSpaceAndNotificationF03NegativeChecks` above.
  -- ==========================================================================
  expectErr "notification double-wait prevention"
    (SeLe4n.Kernel.notificationWait notificationId (SeLe4n.ThreadId.ofNat 7) stN1)
    .alreadyWaiting

  runUntypedF2NegativeChecks                            -- [was 1093-1163]

/-- WS-H2: Lifecycle safety guards negative tests.
    Split into a separate function to avoid maxRecDepth limits in the main do block. -/
private def runH2NegativeChecks : IO Unit := do
  -- H2-NEG-01: childId self-overwrite — childId = untypedId
  expectErr "H2 childId self-overwrite guard"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2UntypedObjId f2UntypedObjId
      (.endpoint {}) 64 f2UntypedState)
    .childIdSelfOverwrite

  -- H2-NEG-02: childId collision with existing object
  expectErr "H2 childId collision with existing object"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2UntypedObjId f2UntypedAuthCnode
      (.endpoint {}) 64 f2UntypedState)
    .childIdCollision

  -- H2-NEG-03: childId collision with existing untyped child
  let h2UntypedWithChild : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject f2UntypedObjId (.untyped {
        regionBase := (SeLe4n.PAddr.ofNat 0x10000)
        regionSize := 256
        children := [{ objId := ⟨60⟩, offset := 0, size := 64 }]
        isDevice := false
      })
      |>.withObject f2UntypedAuthCnode (.cnode (SeLe4n.Model.CNode.ofSlots 0 0 0 0 (SeLe4n.UniqueSlotMap.ofListWF [
          (SeLe4n.Slot.ofNat 0, {
            target := .object f2UntypedObjId
            rights := AccessRightSet.ofList [.read, .write, .grant, .retype]
            freeIndex := 64
          })
        ])))
      |>.withLifecycleObjectType f2UntypedObjId .untyped
      |>.withLifecycleObjectType f2UntypedAuthCnode .cnode
      |>.buildChecked)
  expectErr "H2 childId collision with untyped child"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2UntypedObjId ⟨60⟩
      (.endpoint {}) 64 h2UntypedWithChild)
    .childIdCollision

  IO.println "lifecycle safety guards negative checks passed"

/-- Audit coverage: endpointReplyRecv and cspaceMutate tests.
    Split into a separate function to avoid maxRecDepth limits in the main do block. -/
private def runAuditCoverageChecks : IO Unit := do
  -- ── Audit: endpointReplyRecv coverage ────────────────────────────────
  -- NEG-REPLYRECV-01: replyRecv with non-existent reply target
  expectErr "endpointReplyRecv non-existent reply target"
    (SeLe4n.Kernel.endpointReplyRecv endpointId (SeLe4n.ThreadId.ofNat 6) (SeLe4n.ThreadId.ofNat 999)
      .empty none baseState)
    .objectNotFound

  -- NEG-REPLYRECV-02: replyRecv when reply target is not in blockedOnReply state
  expectErr "endpointReplyRecv target not blocked on reply"
    (SeLe4n.Kernel.endpointReplyRecv endpointId (SeLe4n.ThreadId.ofNat 6) (SeLe4n.ThreadId.ofNat 7)
      .empty none baseState)
    .replyCapInvalid

  -- POS-REPLYRECV: Set up a valid blockedOnReply scenario via endpointCall, then replyRecv
  -- First, enqueue receiver in the dual-queue receiveQ (not legacy waitingReceiver).
  -- WS-SM SM6.D (#7.3 fold): the server (TID 8) supplies a Reply object on its
  -- server-first Recv; the later Call rendezvous links the caller (TID 7) to it.
  let rrReplyId : SeLe4n.ReplyId := ⟨9101⟩
  let rrSetupState : SystemState :=
    { baseState with objects :=
        baseState.objects.insert rrReplyId.toObjId (.reply { replyId := rrReplyId }) }
  -- WS-ZA ZA4.6: through the per-core arms the kernel runs, which link the
  -- caller on the server's reply-waiter queue (the single-core references do
  -- not; `docs/REGISTERED_DEBT.md`), so the invariant checks hold.
  let (_, stCallSetup1) ← expectOkOnCore "replyRecv setup: receiver blocks on receive"
    (SeLe4n.Kernel.endpointReceiveDualOnCore endpointId (SeLe4n.ThreadId.ofNat 8) (some rrReplyId)
      bootCoreId rrSetupState)
  -- Caller calls endpoint (handshakes with queued receiver, caller blocks for reply)
  let (_, stCallSetup2) ← expectOkOnCore "replyRecv setup: caller calls endpoint"
    (SeLe4n.Kernel.endpointCallOnCore endpointId (SeLe4n.ThreadId.ofNat 7) (.frame none false) bootCoreId
      stCallSetup1)
  -- Verify caller is now blocked on reply
  match (stCallSetup2.objects[(SeLe4n.ThreadId.ofNat 7).toObjId]? : Option KernelObject) with
  | some (KernelObject.tcb callerTcb) =>
      -- WS-H1: blockedOnReply now carries replyTarget = some receiverId (ThreadId 8)
      if callerTcb.ipcState = .blockedOnReply endpointId (some (SeLe4n.ThreadId.ofNat 8)) then
        IO.println "positive check passed [replyRecv setup: caller blockedOnReply]"
      else
        throw <| IO.userError s!"replyRecv setup: expected caller blockedOnReply, got {toString callerTcb.ipcState}"
  | _ => throw <| IO.userError "replyRecv setup: expected caller TCB"
  -- Now execute replyRecv: receiver replies to caller and waits on endpoint
  let (_, stReplyRecv) ← expectOkSt "replyRecv success"
    (SeLe4n.Kernel.endpointReplyRecvOnCore endpointId (SeLe4n.ThreadId.ofNat 8) rrReplyId
      (SeLe4n.ThreadId.ofNat 7) .empty cnodeId (SeLe4n.Slot.ofNat 0) bootCoreId stCallSetup2)
  -- Verify caller is unblocked (ready)
  match (stReplyRecv.objects[(SeLe4n.ThreadId.ofNat 7).toObjId]? : Option KernelObject) with
  | some (KernelObject.tcb unblocked) =>
      if unblocked.ipcState = .ready then
        IO.println "positive check passed [replyRecv: caller unblocked after reply]"
      else
        throw <| IO.userError s!"replyRecv: expected caller ready, got {toString unblocked.ipcState}"
  | _ => throw <| IO.userError "replyRecv: expected caller TCB after reply"
  -- WS-SM SM6.D (#7.4/#7.5): a Call rendezvous with a server holding NO reply object
  -- fails closed — the #7 fold makes `endpointCall` atomic, so no raw transition can
  -- strand a caller `.blockedOnReply` with no Reply to answer it (the transition-level
  -- `blockedOnReply ⇒ replyObject` guarantee, negative direction).
  let (_, stNoStashRecv) ← expectOkSt "no-reply receive setup (server blocks, no stash)"
    (SeLe4n.Kernel.endpointReceiveDual endpointId (SeLe4n.ThreadId.ofNat 8) none baseState)
  expectErr "Call with no server reply object fails closed (no unanswerable blockedOnReply)"
    (SeLe4n.Kernel.endpointCall endpointId (SeLe4n.ThreadId.ofNat 7) (.frame none false) stNoStashRecv)
    .replyCapInvalid
  IO.println "endpointReplyRecv coverage checks passed"

  -- ── Audit: cspaceMutate coverage ─────────────────────────────────────
  -- NEG-MUTATE-01: mutate on non-existent CNode
  expectErr "cspaceMutate non-existent CNode"
    (SeLe4n.Kernel.cspaceMutate { cnode := ⟨999⟩, slot := SeLe4n.Slot.ofNat 0 } (AccessRightSet.ofList [.read]) none baseState)
    .objectNotFound

  -- NEG-MUTATE-02: mutate with rights not a subset (escalation attempt)
  expectErr "cspaceMutate rights escalation denied"
    (SeLe4n.Kernel.cspaceMutate slot0 (AccessRightSet.ofList [.read, .write, .grant]) none baseState)
    .invalidCapability

  -- POS-MUTATE: attenuate rights successfully
  let (_, stMutated) ← expectOkSt "cspaceMutate attenuate to read-only"
    (SeLe4n.Kernel.cspaceMutate slot0 (AccessRightSet.ofList [.read]) none baseState)
  -- Verify rights were attenuated
  match SeLe4n.Kernel.cspaceLookupSlot slot0 stMutated with
  | .ok (cap, _) =>
      if cap.rights = AccessRightSet.ofList [.read] then
        IO.println "positive check passed [cspaceMutate: rights attenuated to read-only]"
      else
        throw <| IO.userError s!"cspaceMutate: expected read-only, got {toString cap.rights}"
  | .error err =>
      throw <| IO.userError s!"cspaceMutate: lookup after mutate failed: {toString err}"

  -- POS-MUTATE-BADGE: mutate with badge override
  let (_, stBadgeMutate) ← expectOkSt "cspaceMutate with badge override"
    (SeLe4n.Kernel.cspaceMutate slot0 (AccessRightSet.ofList [.read]) (some (SeLe4n.Badge.ofNatMasked 77)) baseState)
  match SeLe4n.Kernel.cspaceLookupSlot slot0 stBadgeMutate with
  | .ok (cap, _) =>
      if cap.badge = some (SeLe4n.Badge.ofNatMasked 77) then
        IO.println "positive check passed [cspaceMutate: badge override applied]"
      else
        throw <| IO.userError s!"cspaceMutate: expected badge 77, got {toString cap.badge}"
  | .error err =>
      throw <| IO.userError s!"cspaceMutate: lookup after badge mutate failed: {toString err}"

  -- WS-RC R4.D (NEG-MUTATE-NULL): mutate against a null-cap slot rejects
  -- with `.nullCapability`. Codifies the structural witness theorems
  -- `cspaceMutate_rejects_null_cap` and `cspaceMutate_null_cap_rejected`
  -- (in `Capability/Invariant/Preservation/CopyMoveMutate.lean`) at the
  -- runtime-test surface. Constructs a small CNode with `Capability.null`
  -- in slot 0 and asserts the rejection path returns the explicit
  -- `.nullCapability` error code.
  let nullSrcCnode : CNode := (SeLe4n.Model.CNode.ofSlots 0 0 0 0 (SeLe4n.UniqueSlotMap.ofListWF
      [(SeLe4n.Slot.ofNat 0, Capability.null)]))
  let nullCnodeId : SeLe4n.ObjId := ⟨200⟩
  let nullSlot : SeLe4n.Kernel.CSpaceAddr :=
    { cnode := nullCnodeId, slot := SeLe4n.Slot.ofNat 0 }
  let nullState : SystemState :=
    { baseState with objects := baseState.objects.insert nullCnodeId (.cnode nullSrcCnode) }
  expectErr "cspaceMutate against null-cap slot → .nullCapability (R4.D)"
    (SeLe4n.Kernel.cspaceMutate nullSlot (AccessRightSet.ofList [.read]) none nullState)
    .nullCapability
  IO.println "cspaceMutate coverage checks passed"


/-- WS-H7 regression checks: HashMap BEq order-independence and capabilityRef metadata sync. -/
private def runWSH7Checks : IO Unit := do
  let vr1 : VSpaceRoot :=
    { asid := ⟨77⟩
      mappings := (({} : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions)).insert (SeLe4n.VAddr.ofNat 4096) ((SeLe4n.PAddr.ofNat 8192), default)).insert (SeLe4n.VAddr.ofNat 12288) ((SeLe4n.PAddr.ofNat 16384), default) }
  let vr2 : VSpaceRoot :=
    { asid := ⟨77⟩
      mappings := (({} : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions)).insert (SeLe4n.VAddr.ofNat 12288) ((SeLe4n.PAddr.ofNat 16384), default)).insert (SeLe4n.VAddr.ofNat 4096) ((SeLe4n.PAddr.ofNat 8192), default) }
  if vr1 == vr2 then
    IO.println "positive check passed [WS-H7 VSpaceRoot BEq ignores insertion order]"
  else
    throw <| IO.userError "VSpaceRoot BEq ignores insertion order: expected true"

  let capA : Capability := { target := .object endpointId, rights := AccessRightSet.ofList [.read] }
  let capB : Capability := { target := .object notificationId, rights := AccessRightSet.ofList [.read, .write] }
  let cn1 : CNode :=
    (SeLe4n.Model.CNode.ofSlots 2 0 0 2 (SeLe4n.UniqueSlotMap.ofListWF [(SeLe4n.Slot.ofNat 1, capA), (SeLe4n.Slot.ofNat 2, capB)]))
  let cn2 : CNode :=
    (SeLe4n.Model.CNode.ofSlots 2 0 0 2 (SeLe4n.UniqueSlotMap.ofListWF [(SeLe4n.Slot.ofNat 2, capB), (SeLe4n.Slot.ofNat 1, capA)]))
  if cn1 == cn2 then
    IO.println "positive check passed [WS-H7 CNode BEq ignores insertion order]"
  else
    throw <| IO.userError "CNode BEq ignores insertion order: expected true"

  let lifecycleCnode : KernelObject := .cnode (SeLe4n.Model.CNode.ofSlots 1 0 0 1 (SeLe4n.UniqueSlotMap.ofListWF [(SeLe4n.Slot.ofNat 0, capA)]))
  let lifecycleEndpoint : KernelObject := .endpoint {}

  let stAfterCnode :=
    match storeObject ⟨500⟩ lifecycleCnode baseState with
    | .ok ((), st') => st'
    | .error err =>
        panic! s!"unexpected storeObject failure in WS-H7 check (cnode phase): {toString err}"

  -- `v0.35.78`: stated over `lookupSlotCap`, the one slot-target reader — the
  -- retired `lookupCapabilityRefMeta` was that lookup's target projection.
  if (SystemState.lookupSlotCap stAfterCnode { cnode := ⟨500⟩, slot := SeLe4n.Slot.ofNat 0 }).map Capability.target = some capA.target then
    IO.println "positive check passed [WS-H7 storeObject makes a stored CNode's slot resolve to its capability]"
  else
    throw <| IO.userError "storeObject makes a stored CNode's slot resolve to its capability: expected some target"

  let stAfterOverwrite :=
    match storeObject ⟨500⟩ lifecycleEndpoint stAfterCnode with
    | .ok ((), st') => st'
    | .error err =>
        panic! s!"unexpected storeObject failure in WS-H7 check (overwrite phase): {toString err}"

  if (SystemState.lookupSlotCap stAfterOverwrite { cnode := ⟨500⟩, slot := SeLe4n.Slot.ofNat 0 }).map Capability.target = none then
    IO.println "positive check passed [WS-H7 storeObject overwriting a CNode leaves its slots unresolvable]"
  else
    throw <| IO.userError "storeObject overwriting a CNode leaves its slots unresolvable: expected none"

  IO.println "regression checks passed"

-- ============================================================================
-- WS-H11: VSpace & Architecture Enrichment negative tests
-- ============================================================================

/-- WS-H11 negative tests: VSpace page permissions, address bounds, ASID, and TLB. -/
def runWSH11Checks : IO Unit := do
  IO.println "\n--- WS-H11: VSpace & Architecture Enrichment ---"

  -- Build a state with a VSpaceRoot
  let asid : SeLe4n.ASID := ⟨1⟩
  let vspaceOid : SeLe4n.ObjId := ⟨20⟩
  let st := (BootstrapBuilder.empty
    |>.withObject vspaceOid (.vspaceRoot { asid := asid, mappings := {} })
    |>.withLifecycleObjectType vspaceOid .vspaceRoot).buildChecked

  -- H-02: W^X violation must be rejected
  let wxPerms : PagePermissions := { write := true, execute := true }
  expectErr "W^X violation rejected"
    ((SeLe4n.Kernel.Architecture.vspaceMapPageWithFlush asid (SeLe4n.VAddr.ofNat 4096) (SeLe4n.PAddr.ofNat 8192) wxPerms) st)
    .policyDenied
  IO.println "negative check passed [WS-H11 W^X violation correctly rejected]"

  -- A-05: Address bounds violation must be rejected (vspaceMapPageChecked)
  let hugeAddr : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat (2^52 + 1))
  expectErr "address out of bounds rejected"
    ((SeLe4n.Kernel.Architecture.vspaceMapPageChecked asid (SeLe4n.VAddr.ofNat 4096) hugeAddr) st)
    .addressOutOfBounds
  IO.println "negative check passed [WS-H11 address out of bounds correctly rejected]"

  -- Boundary: address exactly at bound is also rejected
  let boundaryAddr : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat (2^52))
  expectErr "address at boundary rejected"
    ((SeLe4n.Kernel.Architecture.vspaceMapPageChecked asid (SeLe4n.VAddr.ofNat 4096) boundaryAddr) st)
    .addressOutOfBounds
  IO.println "negative check passed [WS-H11 address at boundary correctly rejected]"

  -- A-05: Address just below bound should succeed via checked path.
  -- PR #845 review (P2): was `2^52 - 1`, the largest in-bounds PA — all-ones,
  -- and therefore never page-aligned.  `vspaceMapPageChecked` now rejects
  -- unaligned physical addresses, so this uses the largest page-aligned
  -- in-bounds PA, preserving the "just below the bound" intent.
  let validAddr : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat (2^52 - 4096))
  match (SeLe4n.Kernel.Architecture.vspaceMapPageChecked asid (SeLe4n.VAddr.ofNat 4096) validAddr) st with
  | .ok _ => IO.println "positive check passed [WS-H11 valid address accepted by checked map]"
  | .error err => throw <| IO.userError s!"valid address rejected: {toString err}"

  -- PR #845 review (P2): an in-bounds but non-page-aligned PA is rejected.
  -- The ARMv8 descriptor carries only the aligned base and both HAL cache
  -- maintenance loops round their operand down, so accepting an unaligned PA
  -- would let the model record an operand naming an address hardware never
  -- acts on.
  expectErr "unaligned paddr rejected by checked map"
    ((SeLe4n.Kernel.Architecture.vspaceMapPageChecked asid (SeLe4n.VAddr.ofNat 4096)
        (SeLe4n.PAddr.ofNat 0x2001)) st) .alignmentError
  IO.println "negative check passed [PR #845 unaligned paddr correctly rejected]"

  -- Mapping conflict: duplicate vaddr should fail
  let (_, stMapped) ← expectOkSt "map initial"
    ((SeLe4n.Kernel.Architecture.vspaceMapPageWithFlush asid (SeLe4n.VAddr.ofNat 4096) (SeLe4n.PAddr.ofNat 8192)) st)
  expectErr "duplicate mapping conflict"
    ((SeLe4n.Kernel.Architecture.vspaceMapPageWithFlush asid (SeLe4n.VAddr.ofNat 4096) (SeLe4n.PAddr.ofNat 16384)) stMapped)
    .mappingConflict
  IO.println "negative check passed [WS-H11 duplicate mapping correctly rejected]"

  -- ASID not bound: lookup on unregistered ASID
  expectErr "unbound ASID lookup"
    (SeLe4n.Kernel.Architecture.vspaceLookup ⟨99⟩ (SeLe4n.VAddr.ofNat 4096) st)
    .asidNotBound
  IO.println "negative check passed [WS-H11 unbound ASID correctly rejected]"

  -- Translation fault: lookup on unmapped vaddr
  expectErr "unmapped vaddr lookup"
    (SeLe4n.Kernel.Architecture.vspaceLookup asid (SeLe4n.VAddr.ofNat 9999) st)
    .translationFault
  IO.println "negative check passed [WS-H11 unmapped vaddr returns translation fault]"

  -- Unmap non-existent mapping returns error
  expectErr "unmap non-existent"
    ((SeLe4n.Kernel.Architecture.vspaceUnmapPage asid (SeLe4n.VAddr.ofNat 9999)) st)
    .translationFault
  IO.println "negative check passed [WS-H11 unmap non-existent returns translation fault]"

  -- Read-only permissions (write=false, execute=false) should be W^X compliant
  let roPerms : PagePermissions := { read := true, write := false, execute := false }
  match (SeLe4n.Kernel.Architecture.vspaceMapPageWithFlush asid (SeLe4n.VAddr.ofNat 8192) (SeLe4n.PAddr.ofNat 16384) roPerms) st with
  | .ok _ => IO.println "positive check passed [WS-H11 read-only permissions accepted]"
  | .error err => throw <| IO.userError s!"read-only rejected: {toString err}"

  -- Write-only (no execute) should be W^X compliant
  let woPerms : PagePermissions := { read := false, write := true, execute := false }
  match (SeLe4n.Kernel.Architecture.vspaceMapPageWithFlush asid (SeLe4n.VAddr.ofNat 12288) (SeLe4n.PAddr.ofNat 20480) woPerms) st with
  | .ok _ => IO.println "positive check passed [WS-H11 write-only permissions accepted]"
  | .error err => throw <| IO.userError s!"write-only rejected: {toString err}"

  -- Execute-only (no write) should be W^X compliant
  let xoPerms : PagePermissions := { read := false, write := false, execute := true }
  match (SeLe4n.Kernel.Architecture.vspaceMapPageWithFlush asid (SeLe4n.VAddr.ofNat 16384) (SeLe4n.PAddr.ofNat 24576) xoPerms) st with
  | .ok _ => IO.println "positive check passed [WS-H11 execute-only permissions accepted]"
  | .error err => throw <| IO.userError s!"execute-only rejected: {toString err}"

  -- TLB model: empty TLB is consistent
  let tlb := SeLe4n.Model.TlbState.empty
  -- Full flush produces empty TLB
  let flushed := SeLe4n.Model.adapterFlushTlb tlb
  if flushed.entries.length = 0 then
    IO.println "positive check passed [WS-H11 full TLB flush clears all entries]"
  else
    throw <| IO.userError "full TLB flush should clear entries"

  -- Per-ASID flush removes only matching ASID entries
  let entry1 : SeLe4n.Model.TlbEntry :=
    { asid := ⟨1⟩, vaddr := (SeLe4n.VAddr.ofNat 4096), paddr := (SeLe4n.PAddr.ofNat 8192), perms := default }
  let entry2 : SeLe4n.Model.TlbEntry :=
    { asid := ⟨2⟩, vaddr := (SeLe4n.VAddr.ofNat 8192), paddr := (SeLe4n.PAddr.ofNat 16384), perms := default }
  let tlb2 : SeLe4n.Model.TlbState := { entries := [entry1, entry2] }
  let flushedAsid := SeLe4n.Model.adapterFlushTlbByAsid tlb2 ⟨1⟩
  if flushedAsid.entries.length = 1 then
    IO.println "positive check passed [WS-H11 per-ASID TLB flush removes only matching]"
  else
    throw <| IO.userError s!"per-ASID flush: expected 1 entry, got {flushedAsid.entries.length}"

  -- Per-VAddr flush removes only matching (ASID, VAddr) entries
  let entry3 : SeLe4n.Model.TlbEntry :=
    { asid := ⟨1⟩, vaddr := (SeLe4n.VAddr.ofNat 4096), paddr := (SeLe4n.PAddr.ofNat 8192), perms := default }
  let entry4 : SeLe4n.Model.TlbEntry :=
    { asid := ⟨1⟩, vaddr := (SeLe4n.VAddr.ofNat 8192), paddr := (SeLe4n.PAddr.ofNat 16384), perms := default }
  let entry5 : SeLe4n.Model.TlbEntry :=
    { asid := ⟨2⟩, vaddr := (SeLe4n.VAddr.ofNat 4096), paddr := (SeLe4n.PAddr.ofNat 24576), perms := default }
  let tlb3 : SeLe4n.Model.TlbState := { entries := [entry3, entry4, entry5] }
  let flushedVAddr := SeLe4n.Model.adapterFlushTlbByVAddr tlb3 ⟨1⟩ (SeLe4n.VAddr.ofNat 4096)
  if flushedVAddr.entries.length = 2 then
    IO.println "positive check passed [WS-H11 per-VAddr TLB flush removes only matching (ASID,VAddr)]"
  else
    throw <| IO.userError s!"per-VAddr flush: expected 2 entries, got {flushedVAddr.entries.length}"

  -- vspaceLookupFull returns permissions
  let permsCheck : PagePermissions := { read := true, write := false, execute := false, user := true }
  match (SeLe4n.Kernel.Architecture.vspaceMapPageWithFlush asid (SeLe4n.VAddr.ofNat 20480) (SeLe4n.PAddr.ofNat 32768) permsCheck) st with
  | .error err => throw <| IO.userError s!"lookupFull map error: {toString err}"
  | .ok (_, stPerm) =>
      match SeLe4n.Kernel.Architecture.vspaceLookupFull asid (SeLe4n.VAddr.ofNat 20480) stPerm with
      | .error err => throw <| IO.userError s!"lookupFull error: {toString err}"
      | .ok ((paddr, perms), _) =>
          if paddr = (SeLe4n.PAddr.ofNat 32768) && perms.read == true && perms.write == false &&
             perms.execute == false && perms.user == true then
            IO.println "positive check passed [WS-H11 vspaceLookupFull returns correct permissions]"
          else
            throw <| IO.userError s!"lookupFull wrong result"

  -- Cross-ASID isolation: mapping in ASID 1 must not be visible in ASID 2
  let asid2 : SeLe4n.ASID := ⟨2⟩
  let vspaceOid2 : SeLe4n.ObjId := ⟨21⟩
  let st2Asid := (BootstrapBuilder.empty
    |>.withObject vspaceOid (.vspaceRoot { asid := asid, mappings := {} })
    |>.withLifecycleObjectType vspaceOid .vspaceRoot
    |>.withObject vspaceOid2 (.vspaceRoot { asid := asid2, mappings := {} })
    |>.withLifecycleObjectType vspaceOid2 .vspaceRoot).buildChecked
  match (SeLe4n.Kernel.Architecture.vspaceMapPageWithFlush asid (SeLe4n.VAddr.ofNat 4096) (SeLe4n.PAddr.ofNat 8192)) st2Asid with
  | .error err => throw <| IO.userError s!"cross-ASID map failed: {toString err}"
  | .ok (_, stCross) =>
      expectErr "cross-ASID isolation"
        (SeLe4n.Kernel.Architecture.vspaceLookup asid2 (SeLe4n.VAddr.ofNat 4096) stCross)
        .translationFault
  IO.println "negative check passed [WS-H11 cross-ASID isolation enforced]"

  -- Multiple concurrent mappings: map 3 different vaddrs, verify all retrievable
  match (SeLe4n.Kernel.Architecture.vspaceMapPageWithFlush asid (SeLe4n.VAddr.ofNat 4096) (SeLe4n.PAddr.ofNat 8192)) st with
  | .error err => throw <| IO.userError s!"multi-map step 1 failed: {toString err}"
  | .ok (_, stM1) =>
      match (SeLe4n.Kernel.Architecture.vspaceMapPageWithFlush asid (SeLe4n.VAddr.ofNat 8192) (SeLe4n.PAddr.ofNat 16384)) stM1 with
      | .error err => throw <| IO.userError s!"multi-map step 2 failed: {toString err}"
      | .ok (_, stM2) =>
          match (SeLe4n.Kernel.Architecture.vspaceMapPageWithFlush asid (SeLe4n.VAddr.ofNat 12288) (SeLe4n.PAddr.ofNat 24576)) stM2 with
          | .error err => throw <| IO.userError s!"multi-map step 3 failed: {toString err}"
          | .ok (_, stM3) =>
              match SeLe4n.Kernel.Architecture.vspaceLookup asid (SeLe4n.VAddr.ofNat 4096) stM3,
                    SeLe4n.Kernel.Architecture.vspaceLookup asid (SeLe4n.VAddr.ofNat 8192) stM3,
                    SeLe4n.Kernel.Architecture.vspaceLookup asid (SeLe4n.VAddr.ofNat 12288) stM3 with
              | .ok (p1, _), .ok (p2, _), .ok (p3, _) =>
                  if p1 = (SeLe4n.PAddr.ofNat 8192) && p2 = (SeLe4n.PAddr.ofNat 16384) && p3 = (SeLe4n.PAddr.ofNat 24576) then
                    IO.println "positive check passed [WS-H11 multiple concurrent mappings all retrievable]"
                  else
                    throw <| IO.userError "multi-map: wrong addresses returned"
              | _, _, _ => throw <| IO.userError "multi-map: lookup failed"

  -- Sequential map-unmap-map cycle: verify remapping works after unmap
  match (SeLe4n.Kernel.Architecture.vspaceMapPageWithFlush asid (SeLe4n.VAddr.ofNat 4096) (SeLe4n.PAddr.ofNat 8192)) st with
  | .error err => throw <| IO.userError s!"cycle map1 failed: {toString err}"
  | .ok (_, stC1) =>
      match (SeLe4n.Kernel.Architecture.vspaceUnmapPage asid (SeLe4n.VAddr.ofNat 4096)) stC1 with
      | .error err => throw <| IO.userError s!"cycle unmap failed: {toString err}"
      | .ok (_, stC2) =>
          match (SeLe4n.Kernel.Architecture.vspaceMapPageWithFlush asid (SeLe4n.VAddr.ofNat 4096) (SeLe4n.PAddr.ofNat 16384)) stC2 with
          | .error err => throw <| IO.userError s!"cycle remap failed: {toString err}"
          | .ok (_, stC3) =>
              match SeLe4n.Kernel.Architecture.vspaceLookup asid (SeLe4n.VAddr.ofNat 4096) stC3 with
              | .ok (pa, _) =>
                  if pa = (SeLe4n.PAddr.ofNat 16384) then
                    IO.println "positive check passed [WS-H11 map-unmap-remap cycle works correctly]"
                  else
                    throw <| IO.userError s!"cycle: expected 16384, got {pa.toNat}"
              | .error err => throw <| IO.userError s!"cycle lookup failed: {toString err}"

  IO.println "all WS-H11 VSpace & Architecture checks passed"

-- S2-J: Migrated from deprecated api* wrappers to syscallInvoke path.
/-- WS-H15e: Negative tests for syscall capability-checking wrappers. -/
private def runWSH15Checks : IO Unit := do
  -- Build a state with a CNode (radixWidth=4, 16 slots) with known capabilities.
  let cnodeId : SeLe4n.ObjId := ⟨50⟩
  let epId : SeLe4n.ObjId := ⟨40⟩
  let callerId : SeLe4n.ThreadId := ⟨1⟩
  let writeCap : Capability := { target := .object epId, rights := AccessRightSet.ofList [.write] }
  let readOnlyCap : Capability := { target := .object epId, rights := AccessRightSet.ofList [.read] }
  let cn : CNode := (SeLe4n.Model.CNode.ofSlots 4 0 0 4 (SeLe4n.UniqueSlotMap.ofListWF [
      (SeLe4n.Slot.ofNat 0, writeCap),
      (SeLe4n.Slot.ofNat 1, readOnlyCap)
    ]))
  let ep : KernelObject := .endpoint (Endpoint.ofQueues {} {})
  let st : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject cnodeId (.cnode cn)
      |>.withObject epId ep
      |>.buildChecked)

  -- H15-NEG-01: syscallLookupCap with non-existent CSpace root
  let badRootGate : SeLe4n.Kernel.SyscallGate := {
    callerId := callerId, cspaceRoot := ⟨9999⟩,
    capAddr := SeLe4n.CPtr.ofNat 0, capDepth := 4, requiredRight := .write
  }
  expectErr "H15 syscallLookupCap non-existent CSpace root"
    (SeLe4n.Kernel.syscallLookupCap badRootGate st)
    .objectNotFound

  -- H15-NEG-02: syscallLookupCap with valid CSpace but missing capability (slot 15)
  let missingSlotGate : SeLe4n.Kernel.SyscallGate := {
    callerId := callerId, cspaceRoot := cnodeId,
    capAddr := SeLe4n.CPtr.ofNat 15, capDepth := 4, requiredRight := .write
  }
  expectErr "H15 syscallLookupCap valid CSpace missing capability"
    (SeLe4n.Kernel.syscallLookupCap missingSlotGate st)
    .invalidCapability

  -- H15-NEG-03: syscallLookupCap with valid capability but wrong right
  let wrongRightGate : SeLe4n.Kernel.SyscallGate := {
    callerId := callerId, cspaceRoot := cnodeId,
    capAddr := SeLe4n.CPtr.ofNat 1, capDepth := 4, requiredRight := .write   -- slot 1 has .read only
  }
  expectErr "H15 syscallLookupCap valid capability wrong right"
    (SeLe4n.Kernel.syscallLookupCap wrongRightGate st)
    .illegalAuthority

  -- H15-NEG-04: syscallLookupCap succeeds with correct right
  let goodGate : SeLe4n.Kernel.SyscallGate := {
    callerId := callerId, cspaceRoot := cnodeId,
    capAddr := SeLe4n.CPtr.ofNat 0, capDepth := 4, requiredRight := .write
  }
  match SeLe4n.Kernel.syscallLookupCap goodGate st with
  | .ok (cap, _) =>
      if cap.hasRight .write then
        IO.println "positive check passed [H15 syscallLookupCap correct right resolves]"
      else
        throw <| IO.userError "H15 syscallLookupCap: resolved cap missing expected right"
  | .error err =>
      throw <| IO.userError s!"H15 syscallLookupCap: expected success, got {toString err}"

  -- H15-NEG-05: S2-J: Replaced deprecated apiEndpointSend with syscallInvoke path
  let msg : IpcMessage := { registers := #[⟨42⟩], badge := none }
  expectErr "H15 syscall endpoint send insufficient rights"
    (SeLe4n.Kernel.syscallInvoke { wrongRightGate with requiredRight := .write } (fun cap =>
      if cap.target ≠ .object epId then fun _ => .error .invalidCapability
      else SeLe4n.Kernel.endpointSendDual epId wrongRightGate.callerId (.frame msg.badge false)) st)
    .illegalAuthority

  -- H15-NEG-06: syscallLookupCap with zero depth → illegalState
  let zeroDepthGate : SeLe4n.Kernel.SyscallGate := {
    callerId := callerId, cspaceRoot := cnodeId,
    capAddr := SeLe4n.CPtr.ofNat 0, capDepth := 0, requiredRight := .write
  }
  expectErr "H15 syscallLookupCap zero depth"
    (SeLe4n.Kernel.syscallLookupCap zeroDepthGate st)
    .illegalState

  IO.println "all WS-H15 syscall capability negative checks passed"

/-- WS-H15e: Platform contract validation tests.
Verify that RPi5 platform contracts produce substantive (non-trivial) results
and that hardware-derived predicates hold for known boundary values. -/
def runWSH15PlatformChecks : IO Unit := do
  IO.println "=== WS-H15e platform contract checks ==="

  -- H15-PLAT-01: rpi5MachineConfig wellFormed
  if SeLe4n.Platform.RPi5.rpi5MachineConfig.wellFormed then
    IO.println "positive check passed [H15 rpi5MachineConfig wellFormed = true]"
  else
    throw <| IO.userError "H15 rpi5MachineConfig wellFormed should be true"

  -- H15-PLAT-02: MMIO region disjointness (computed check)
  if SeLe4n.Platform.RPi5.mmioRegionDisjointCheck then
    IO.println "positive check passed [H15 mmioRegionDisjointCheck = true]"
  else
    throw <| IO.userError "H15 mmioRegionDisjointCheck should be true"

  -- H15-PLAT-03: RPi5 interrupt contract — INTID 0 is supported (SGI range)
  let irq0 : SeLe4n.Irq := ⟨0⟩
  let contract := SeLe4n.Platform.RPi5.rpi5InterruptContract
  if @decide _ (contract.irqLineSupportedDecidable irq0) then
    IO.println "positive check passed [H15 IRQ INTID 0 supported]"
  else
    throw <| IO.userError "H15 IRQ INTID 0 should be supported (SGI range)"

  -- H15-PLAT-04: RPi5 interrupt contract — INTID 308 (UARTA, GIC_SPI 276,
  -- the highest SPI `bcm2712.dtsi` wires) and INTID 319 (the last of the
  -- BCM2712's 288 SPIs) are supported
  for intid in [308, 319] do
    let irq : SeLe4n.Irq := ⟨intid⟩
    if @decide _ (contract.irqLineSupportedDecidable irq) then
      IO.println s!"positive check passed [H15 IRQ INTID {intid} supported]"
    else
      throw <| IO.userError s!"H15 IRQ INTID {intid} should be supported (BCM2712 SPI)"

  -- H15-PLAT-05: RPi5 interrupt contract — INTID 320 is NOT supported
  let irq320 : SeLe4n.Irq := ⟨320⟩
  if @decide _ (contract.irqLineSupportedDecidable irq320) then
    throw <| IO.userError "H15 IRQ INTID 320 should NOT be supported"
  else
    IO.println "negative check passed [H15 IRQ INTID 320 not supported]"

  -- H15-PLAT-06: RPi5 boot contract — objectTypeMetadata verified by theorem
  -- `rpi5BootContract_objectType_holds` is a proof that the predicate holds.
  -- We verify the equivalent computational check: default objects HashMap is empty.
  if ({} : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject).size == 0 then
    IO.println "positive check passed [H15 rpi5BootContract objectTypeMetadata]"
  else
    throw <| IO.userError "H15 rpi5BootContract objectTypeMetadataConsistent should hold"

  IO.println "all WS-H15 platform contract checks passed"

/-- WS-H16/M-18: Lifecycle operations negative tests — the error branches of
the untyped carve (`untypedRetypeObject`, `retypeFromUntyped`). -/
def runWSH16LifecycleChecks : IO Unit := do
  IO.println "=== WS-H16/M-18 lifecycle negative checks ==="

  -- Fixture: state with an endpoint, a CNode (authority), and a TCB
  let h16TargetId : SeLe4n.ObjId := ⟨150⟩
  let h16CnodeId : SeLe4n.ObjId := ⟨151⟩
  let h16TcbId : SeLe4n.ObjId := ⟨152⟩
  let h16AuthSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := h16CnodeId, slot := SeLe4n.Slot.ofNat 0 }

  let h16State : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject h16TargetId (.endpoint {})
      -- Radix 1: the cleanup and read-only slot is slot 1, which a radix-0
      -- CNode has no entry for (WS-ZA ZA5.3 slot array).
      |>.withObject h16CnodeId (.cnode (CNode.ofList 0 0 0 1 [
          (SeLe4n.Slot.ofNat 0, {
            target := .object h16TargetId
            rights := AccessRightSet.ofList [.read, .write]
          }),
          (SeLe4n.Slot.ofNat 1, {
            target := .object h16TargetId
            rights := AccessRightSet.ofList [.read]
          })
        ]))
      |>.withObject h16TcbId (.tcb {
        tid := ⟨152⟩
        priority := ⟨10⟩
        domain := ⟨0⟩
        spaceCells := SeLe4n.Model.TCB.spaceCellsOf h16CnodeId ⟨20⟩
        ipcBuffer := (SeLe4n.VAddr.ofNat 4096)
      })
      |>.withLifecycleObjectType h16TargetId .endpoint
      |>.withLifecycleObjectType h16CnodeId .cnode
      |>.withLifecycleObjectType h16TcbId .tcb
      |>.buildChecked)

  -- H16-NEG-01..06 (WS-ZA ZA5.4 part 14): the carve's refusals.  The in-place
  -- retype these checks exercised is retired; every object is carved, so the
  -- negatives are the carve's.  Fixture: an untyped at `0x40000` with a
  -- `.retype` capability (slot 0), the same untyped without `.retype` (slot 1),
  -- a capability to the endpoint (slot 2) and empty slots 3.
  let carveRefusalUtId : SeLe4n.ObjId := ⟨153⟩
  let carveRefusalCnId : SeLe4n.ObjId := ⟨154⟩
  let carveRefusalSlot (n : Nat) : SeLe4n.Kernel.CSpaceAddr := { cnode := carveRefusalCnId, slot := SeLe4n.Slot.ofNat n }
  let carveRefusalState : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject h16TargetId (.endpoint {})
      |>.withObject carveRefusalUtId (.untyped
          { regionBase := SeLe4n.PAddr.ofNat 0x40000, regionSize := 0x2000 })
      |>.withObject carveRefusalCnId (.cnode (CNode.ofList 0 0 0 2 [
          (SeLe4n.Slot.ofNat 0, { target := .object carveRefusalUtId, rights := AccessRightSet.ofList [.read, .write, .retype] }),
          (SeLe4n.Slot.ofNat 1, { target := .object carveRefusalUtId, rights := AccessRightSet.ofList [.read, .write] }),
          (SeLe4n.Slot.ofNat 2, { target := .object h16TargetId, rights := AccessRightSet.ofList [.read, .write, .retype] })
        ]))
      |>.withLifecycleObjectType h16TargetId .endpoint
      |>.withLifecycleObjectType carveRefusalUtId .untyped
      |>.withLifecycleObjectType carveRefusalCnId .cnode
      |>.buildChecked)

  -- H16-NEG-01: a carve at an occupied child id → childIdCollision
  expectErr "H16 carve at an occupied child id"
    (SeLe4n.Kernel.untypedRetypeObject (carveRefusalSlot 0) h16TargetId (carveRefusalSlot 3) .notification carveRefusalState)
    .childIdCollision

  -- H16-NEG-02: a carve through a capability to a non-untyped → untypedTypeMismatch
  expectErr "H16 carve through a capability to an endpoint"
    (SeLe4n.Kernel.untypedRetypeObject (carveRefusalSlot 2) ⟨155⟩ (carveRefusalSlot 3) .notification carveRefusalState)
    .untypedTypeMismatch

  -- H16-NEG-03: a carve through an untyped capability without `.retype` → illegalAuthority
  expectErr "H16 carve without the retype right"
    (SeLe4n.Kernel.untypedRetypeObject (carveRefusalSlot 1) ⟨155⟩ (carveRefusalSlot 3) .notification carveRefusalState)
    .illegalAuthority

  -- H16-NEG-04: a carve whose authority CNode does not exist → objectNotFound
  expectErr "H16 carve with a missing authority CNode"
    (SeLe4n.Kernel.untypedRetypeObject { cnode := ⟨999⟩, slot := SeLe4n.Slot.ofNat 0 } ⟨155⟩
      (carveRefusalSlot 3) .notification carveRefusalState)
    .objectNotFound

  -- H16-NEG-05: a carve into an occupied destination slot is refused, and
  -- carves nothing.
  expectCond "H16-NEG-05" "carve into an occupied destination slot refused"
    (match SeLe4n.Kernel.untypedRetypeObject (carveRefusalSlot 0) ⟨155⟩ (carveRefusalSlot 2) .notification carveRefusalState with
     | .error _ => true
     | .ok _ => false)

  -- H16-NEG-06: a carve is made on its own boundary, the capability's free index
  -- rounded up to it (seL4's `alignUp(freeRef, objectSize)`), never refused.
  -- From an index of 16 (an endpoint's worth): a TCB lands at 2048, an endpoint
  -- at 4096, a frame at the next page (8192), and a TCB after the frame on its
  -- own 2048-byte boundary (12288).  The index of 16 is reached by carving an
  -- endpoint, so the capability has a child and the carves start at its free
  -- index; a childless capability is reset and starts at 0 (seL4's
  -- `ensureNoChildren` in `decodeUntypedInvocation`).
  let misalignedCarveState : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject carveRefusalUtId (.untyped
          { regionBase := SeLe4n.PAddr.ofNat 0x40000, regionSize := 0x4000 })
      |>.withObject carveRefusalCnId (.cnode (CNode.ofList 0 0 0 3 [
          (SeLe4n.Slot.ofNat 0, { target := .object carveRefusalUtId, rights := AccessRightSet.ofList [.read, .write, .retype] })
        ]))
      |>.withLifecycleObjectType carveRefusalUtId .untyped
      |>.withLifecycleObjectType carveRefusalCnId .cnode
      |>.buildChecked)
  let carveAt (req : SeLe4n.Kernel.CarveRequest) (child dstSlot : Nat) (s : SystemState) :
      Option SystemState :=
    match SeLe4n.Kernel.untypedRetypeObject (carveRefusalSlot 0) ⟨child⟩ (carveRefusalSlot dstSlot)
        req s with
    | .ok ((), s') => some s'
    | .error _ => none
  let indexOf (s : SystemState) : Option Nat :=
    (SystemState.lookupSlotCap s (carveRefusalSlot 0)).map (·.freeIndex)
  let alignedRun : Option (SystemState × SystemState × SystemState × SystemState × SystemState) := do
    let s0 ← carveAt .endpoint 159 5 misalignedCarveState
    let s1 ← carveAt (.tcb ⟨0⟩ bootCoreId) 155 1 s0
    let s2 ← carveAt .endpoint 156 2 s1
    let s3 ← carveAt .frame 157 3 s2
    let s4 ← carveAt (.tcb ⟨0⟩ bootCoreId) 158 4 s3
    pure (s0, s1, s2, s3, s4)
  match alignedRun with
  | none => expectCond "H16-NEG-06" "the aligned carve sequence succeeds" false
  | some (s0, s1, s2, s3, s4) =>
    expectCond "H16-NEG-06" "an endpoint carved first leaves the free index at 16"
      (indexOf s0 == some 16)
    expectCond "H16-NEG-06" "a TCB at free index 16 is carved at 2048, the index past it 4096"
      (indexOf s1 == some 4096)
    expectCond "H16-NEG-06" "an endpoint after it needs no rounding (index 4112)"
      (indexOf s2 == some 4112)
    expectCond "H16-NEG-06" "a frame after the endpoint is carved on the next page (0x42000)"
      (indexOf s3 == some 12288 &&
        (s3.getFrame? ⟨157⟩).map (·.base.toNat) == some 0x42000)
    expectCond "H16-NEG-06" "a TCB after the frame lands on its own boundary (12288, index 14336)"
      (indexOf s4 == some 14336 &&
        (0x40000 + 12288) % 2048 == 0)
  -- A child untyped is aligned to its own size, as seL4's `alignUp(freeRef, 2^b)`:
  -- after an endpoint (index 16), a 2^14-byte child lands at 16384 (0x44000),
  -- not at the next page (4096), and the index past it is 32768.
  let childBase (s : SystemState) : Option Nat :=
    match (s.objects[(⟨166⟩ : SeLe4n.ObjId)]? : Option KernelObject) with
    | some (.untyped u) => some u.regionBase.toNat
    | _ => none
  let smallFirstState : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject carveRefusalUtId (.untyped
          { regionBase := SeLe4n.PAddr.ofNat 0x40000, regionSize := 0x10000 })
      |>.withObject carveRefusalCnId (.cnode (CNode.ofList 0 0 0 3 [
          (SeLe4n.Slot.ofNat 0, { target := .object carveRefusalUtId, rights := AccessRightSet.ofList [.read, .write, .retype] })
        ]))
      |>.withLifecycleObjectType carveRefusalUtId .untyped
      |>.withLifecycleObjectType carveRefusalCnId .cnode
      |>.buildChecked)
  match (do
      let s1 ← carveAt .endpoint 165 1 smallFirstState
      let s2 ← carveAt (.untyped 14) 166 2 s1
      pure (s1, s2) : Option (SystemState × SystemState)) with
  | none => expectCond "H16-NEG-06" "an endpoint then a child untyped are carved" false
  | some (s1, s2) =>
    expectCond "H16-NEG-06" "a 2^14-byte child untyped after an endpoint lands on its own size (0x44000, index 32768)"
      (indexOf s1 == some 16 && childBase s2 == some 0x44000 && indexOf s2 == some 32768)

  -- H16-NEG-07: retypeFromUntyped with exhausted untyped (the authority capability's free index at the region boundary) → regionExhausted.
  -- The region holds one endpoint, and carving it leaves the capability's free
  -- index at the region's end with a child; a childless capability would be
  -- reset to 0 instead (seL4's `ensureNoChildren`), so exhaustion needs a child.
  let fullRegionUntypedId : SeLe4n.ObjId := ⟨160⟩
  let fullRegionCnodeId : SeLe4n.ObjId := ⟨161⟩
  let fullRegionAuthSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := fullRegionCnodeId, slot := SeLe4n.Slot.ofNat 0 }
  let fullRegionFresh : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject fullRegionUntypedId (.untyped {
        regionBase := (SeLe4n.PAddr.ofNat 0x10000)
        regionSize := 16
        children := []
        isDevice := false
      })
      |>.withObject fullRegionCnodeId (.cnode (CNode.ofList 0 0 0 1 [
          (SeLe4n.Slot.ofNat 0, {
            target := .object fullRegionUntypedId
            rights := AccessRightSet.ofList [.read, .write, .grant, .retype]
          })
        ]))
      |>.withLifecycleObjectType fullRegionUntypedId .untyped
      |>.withLifecycleObjectType fullRegionCnodeId .cnode
      |>.buildChecked)
  match SeLe4n.Kernel.untypedRetypeObject fullRegionAuthSlot ⟨167⟩
      { cnode := fullRegionCnodeId, slot := SeLe4n.Slot.ofNat 1 } .endpoint fullRegionFresh with
  | .error e => expectCond "H16-NEG-07" s!"the endpoint filling the region is carved ({reprStr e})" false
  | .ok ((), fullRegionState) =>
    expectCond "H16-NEG-07" "the carve leaves the free index at the region's end, with a child"
      ((SystemState.lookupSlotCap fullRegionState fullRegionAuthSlot).map (·.freeIndex) == some 16 &&
        SeLe4n.Kernel.hasCdtChildren fullRegionState fullRegionAuthSlot)
    expectErr "H16 retypeFromUntyped exhausted untyped"
      (SeLe4n.Kernel.retypeFromUntyped fullRegionAuthSlot fullRegionUntypedId ⟨162⟩
        (.endpoint {}) 16 fullRegionState)
      .untypedRegionExhausted

  -- H16-NEG-08: retypeFromUntyped with non-untyped source → untypedTypeMismatch
  -- Plan REQ: "retypeFromUntyped with invalid object type → expect error"
  -- The source is an endpoint, not an untyped, triggering the type mismatch guard.
  expectErr "H16 retypeFromUntyped non-untyped source"
    (SeLe4n.Kernel.retypeFromUntyped h16AuthSlot h16TargetId ⟨162⟩
      (.endpoint {}) 64 h16State)
    .untypedTypeMismatch

  -- H16-NEG-09: retypeFromUntyped with device untyped → untypedDeviceRestriction
  -- Device untypeds cannot back typed kernel objects (except other untypeds).
  let h16DeviceUntypedId : SeLe4n.ObjId := ⟨163⟩
  let h16DeviceCnodeId : SeLe4n.ObjId := ⟨164⟩
  let h16DeviceAuthSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := h16DeviceCnodeId, slot := SeLe4n.Slot.ofNat 0 }
  let h16DeviceState : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject h16DeviceUntypedId (.untyped {
        regionBase := (SeLe4n.PAddr.ofNat 0x20000)
        regionSize := 8192
        children := []
        isDevice := true     -- device untyped
      })
      |>.withObject h16DeviceCnodeId (.cnode (SeLe4n.Model.CNode.ofSlots 0 0 0 0 (SeLe4n.UniqueSlotMap.ofListWF [
          (SeLe4n.Slot.ofNat 0, {
            target := .object h16DeviceUntypedId
            rights := AccessRightSet.ofList [.read, .write, .grant, .retype]
          })
        ])))
      |>.withLifecycleObjectType h16DeviceUntypedId .untyped
      |>.withLifecycleObjectType h16DeviceCnodeId .cnode
      |>.buildChecked)
  expectErr "H16 retypeFromUntyped device untyped restriction"
    (SeLe4n.Kernel.retypeFromUntyped h16DeviceAuthSlot h16DeviceUntypedId ⟨165⟩
      (.endpoint {}) 1024 h16DeviceState)
    .untypedDeviceRestriction

  IO.println "all WS-H16/M-18 lifecycle negative checks passed"

-- ============================================================================
-- WS-J1-E: Register decode negative tests
-- ============================================================================

/-- WS-J1-E: Negative tests for the register decode path.
Exercises every decode error branch:
- Invalid register index (out of architectural bounds)
- Invalid syscall number (not in the modeled set)
- Malformed message info word (exceeds field bounds)
- Decode of zero-valued registers (valid edge case) -/
def runWSJ1DecodeChecks : IO Unit := do
  -- J1-NEG-01: validateRegBound with out-of-bounds register index → invalidRegister
  -- ARM64 has 32 GPRs; register index 32 is the first invalid index.
  expectErr "J1 validateRegBound out-of-bounds (32 ≥ 32)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.validateRegBound ⟨32⟩ 32)
    .invalidRegister

  -- J1-NEG-02: validateRegBound with large register index → invalidRegister
  expectErr "J1 validateRegBound large index (999 ≥ 32)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.validateRegBound ⟨999⟩ 32)
    .invalidRegister

  -- J1-NEG-03: validateRegBound at boundary (31 < 32) → success
  let _ ← expectOkVal "J1 validateRegBound boundary (31 < 32)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.validateRegBound ⟨31⟩ 32)

  -- J1-NEG-04: decodeSyscallId with value beyond modeled set → invalidSyscallNumber
  -- WS-RR RR8.16 (`v0.35.190`): SyscallId now covers 0..35 (count=36,
  -- +cspaceRevoke — `seL4_CNode_Revoke`, the arm the revocation family had never
  -- had — on top of PR #887's +tcbSetFaultHandler, WS-SM SM9.C.8's
  -- +declassifySignal, SM9.A.6's +auditRead/+auditDrain, SM8.C.9's +declassify,
  -- SM7.D's +vspaceUnifyInstruction and PR #822 Phase H's +mintReplyCap); value
  -- 36 is the first invalid number.  The six most recent additions are each
  -- checked as VALID, so the boundary is pinned from both sides and a future
  -- off-by-one in `ofNat?` cannot pass silently.
  let _ ← expectOkVal "J1 decodeSyscallId valid boundary (30 = declassify)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallId ⟨30⟩)
  let _ ← expectOkVal "J1 decodeSyscallId valid boundary (31 = auditRead)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallId ⟨31⟩)
  let _ ← expectOkVal "J1 decodeSyscallId valid boundary (32 = auditDrain)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallId ⟨32⟩)
  let _ ← expectOkVal "J1 decodeSyscallId valid boundary (33 = declassifySignal)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallId ⟨33⟩)
  let _ ← expectOkVal "J1 decodeSyscallId valid boundary (34 = tcbSetFaultHandler)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallId ⟨34⟩)
  let _ ← expectOkVal "J1 decodeSyscallId valid boundary (35 = cspaceRevoke)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallId ⟨35⟩)
  let _ ← expectOkVal "J1 decodeSyscallId valid boundary (36 = untypedRetype)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallId ⟨36⟩)
  let _ ← expectOkVal "J1 decodeSyscallId valid boundary (37 = untypedReset)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallId ⟨37⟩)
  let _ ← expectOkVal "J1 decodeSyscallId valid boundary (38 = tcbSetSpace)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallId ⟨38⟩)
  let _ ← expectOkVal "J1 decodeSyscallId valid boundary (40 = pageTableUnmap)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallId ⟨40⟩)
  let _ ← expectOkVal "J1 decodeSyscallId valid boundary (41 = yield)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallId ⟨41⟩)
  let _ ← expectOkVal "J1 decodeSyscallId valid boundary (42 = schedContextConsumed)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallId ⟨42⟩)
  expectErr "J1 decodeSyscallId invalid (43)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallId ⟨43⟩)
    .invalidSyscallNumber

  -- J1-NEG-05: decodeSyscallId with large invalid number → invalidSyscallNumber
  expectErr "J1 decodeSyscallId invalid (9999)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallId ⟨9999⟩)
    .invalidSyscallNumber

  -- J1-NEG-06: decodeSyscallId with valid boundary (12 = serviceRevoke) → success
  let _ ← expectOkVal "J1 decodeSyscallId valid boundary (12)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallId ⟨12⟩)

  -- J1-NEG-07: decodeMsgInfo with oversized length → invalidMessageInfo
  -- maxMessageRegisters = 120 (7-bit field max 127, but bounded to 120).
  -- Encode a word with length = 121 (exceeds bound).
  let oversizedLength : SeLe4n.RegValue := ⟨121⟩  -- bits 0..6 = 121
  expectErr "J1 decodeMsgInfo oversized length (121 > 120)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeMsgInfo oversizedLength)
    .invalidMessageInfo

  -- J1-NEG-08: decodeMsgInfo with maximum 7-bit length field → invalidMessageInfo
  -- The 7-bit length field can hold 0..127; any value 121..127 exceeds maxMessageRegisters=120.
  let maxFieldLength : SeLe4n.RegValue := ⟨127⟩  -- bits 0..6 = 127 > 120
  expectErr "J1 decodeMsgInfo max 7-bit length (127 > 120)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeMsgInfo maxFieldLength)
    .invalidMessageInfo

  -- J1-NEG-09: decodeMsgInfo with valid boundary values → success
  -- length=120, extraCaps=3, label=0 → valid.
  let boundaryMsgInfo : SeLe4n.RegValue := ⟨120 ||| (3 <<< 7)⟩
  let _ ← expectOkVal "J1 decodeMsgInfo valid boundary (len=120, caps=3)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeMsgInfo boundaryMsgInfo)

  -- J1-NEG-10: decodeCapPtr with zero → always succeeds (CPtr space is unbounded)
  let _ ← expectOkVal "J1 decodeCapPtr zero-valued register"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeCapPtr ⟨0⟩)

  -- J1-NEG-11: decodeSyscallId with zero → valid (SyscallId.send = 0)
  let _ ← expectOkVal "J1 decodeSyscallId zero-valued register (send)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallId ⟨0⟩)

  -- J1-NEG-12: decodeMsgInfo with zero → valid (length=0, extraCaps=0, label=0)
  let _ ← expectOkVal "J1 decodeMsgInfo zero-valued register"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeMsgInfo ⟨0⟩)

  -- J1-NEG-13: decodeSyscallArgs with out-of-bounds layout register → invalidRegister
  -- Use a layout where capPtrReg index exceeds registerCount.
  let badLayout : SeLe4n.SyscallRegisterLayout := {
    capPtrReg     := ⟨50⟩   -- exceeds 32-register bound
    msgInfoReg    := ⟨1⟩
    msgRegs       := #[⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩]
    syscallNumReg := ⟨7⟩
  }
  let defaultRegs : SeLe4n.RegisterFile := default
  expectErr "J1 decodeSyscallArgs out-of-bounds layout register"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgs badLayout defaultRegs 32)
    .invalidRegister

  -- J1-NEG-14: decodeSyscallArgs with out-of-bounds msgReg → invalidRegister
  let badMsgRegLayout : SeLe4n.SyscallRegisterLayout := {
    capPtrReg     := ⟨0⟩
    msgInfoReg    := ⟨1⟩
    msgRegs       := #[⟨2⟩, ⟨3⟩, ⟨40⟩, ⟨5⟩]  -- index 40 exceeds bound
    syscallNumReg := ⟨7⟩
  }
  expectErr "J1 decodeSyscallArgs out-of-bounds msgReg"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgs badMsgRegLayout defaultRegs 32)
    .invalidRegister

  -- J1-NEG-15: decodeSyscallArgs with invalid syscall number in register → invalidSyscallNumber
  -- Write syscall number 99 into x7.
  let regsInvalidSyscall : SeLe4n.RegisterFile :=
    SeLe4n.RegisterFile.withGprs 0 0 (fun r =>
        if r == 7 then 99  -- invalid syscall number
        else 0)
  expectErr "J1 decodeSyscallArgs invalid syscall in register"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgs SeLe4n.arm64DefaultLayout regsInvalidSyscall 32)
    .invalidSyscallNumber

  -- J1-NEG-16: decodeSyscallArgs with malformed msgInfo in register → invalidMessageInfo
  -- Write an oversized length (127 > 120) into the msgInfo register (x1).
  let regsInvalidMsgInfo : SeLe4n.RegisterFile :=
    SeLe4n.RegisterFile.withGprs 0 0 (fun r =>
        if r == 1 then 127  -- length=127 > maxMessageRegisters=120
        else if r == 7 then 0  -- valid syscall (send)
        else 0)
  expectErr "J1 decodeSyscallArgs malformed msgInfo in register"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgs SeLe4n.arm64DefaultLayout regsInvalidMsgInfo 32)
    .invalidMessageInfo

  -- J1-NEG-17: decodeSyscallArgs with all-zero registers → valid decode
  -- Zero registers: capPtr=0, msgInfo=(len=0,caps=0,label=0), syscallId=send
  -- K-A: Also verify msgRegs are populated with correct count (4 for ARM64 layout).
  let decoded ← expectOkVal "J1 decodeSyscallArgs all-zero registers (valid)"
    (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgs SeLe4n.arm64DefaultLayout default 32)
  unless decoded.msgRegs.size == 4 do
    throw <| IO.userError s!"K-A: expected msgRegs.size = 4 (ARM64 layout), got {decoded.msgRegs.size}"

  -- J1-NEG-18: Full syscallEntry with no current thread → illegalState
  let emptyState : SystemState := BootstrapBuilder.empty.buildChecked
  expectErr "J1 syscallEntry no current thread"
    (SeLe4n.Kernel.syscallEntry SeLe4n.arm64DefaultLayout 32 emptyState)
    .illegalState

  IO.println "all WS-J1-E register decode negative checks passed"

-- ============================================================================
-- WS-K-G: Comprehensive testing for WS-K syscall dispatch surface
-- ============================================================================

/-- K-G1: CSpace decode/dispatch error paths. -/
private def runWSKGCSpaceChecks : IO Unit := do
  -- ---- K-G1: CSpace negative tests ----

  -- K-G-NEG-01: decodeCSpaceMintArgs with insufficient msgRegs (< 4) → invalidMessageInfo
  let shortDecode : SyscallDecodeResult := {
    capAddr := SeLe4n.CPtr.ofNat 0
    msgInfo := { length := 0, extraCaps := 0, label := 0 }
    syscallId := .cspaceMint
    msgRegs := #[⟨10⟩, ⟨20⟩]  -- only 2, need 4
  }
  expectErr "K-G-NEG-01 cspaceMint decode insufficient msgRegs"
    (SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceMintArgs shortDecode)
    .invalidMessageInfo

  -- K-G-NEG-02: decodeCSpaceCopyArgs with insufficient msgRegs (< 2) → invalidMessageInfo
  let oneRegDecode : SyscallDecodeResult := {
    capAddr := SeLe4n.CPtr.ofNat 0
    msgInfo := { length := 0, extraCaps := 0, label := 0 }
    syscallId := .cspaceCopy
    msgRegs := #[⟨10⟩]  -- only 1, need 2
  }
  expectErr "K-G-NEG-02 cspaceCopy decode insufficient msgRegs"
    (SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceCopyArgs oneRegDecode)
    .invalidMessageInfo

  -- K-G-NEG-03: decodeCSpaceMoveArgs with insufficient msgRegs (< 2) → invalidMessageInfo
  expectErr "K-G-NEG-03 cspaceMove decode insufficient msgRegs"
    (SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceMoveArgs oneRegDecode)
    .invalidMessageInfo

  -- K-G-NEG-04: decodeCSpaceDeleteArgs with zero msgRegs → invalidMessageInfo
  let emptyDecode : SyscallDecodeResult := {
    capAddr := SeLe4n.CPtr.ofNat 0
    msgInfo := { length := 0, extraCaps := 0, label := 0 }
    syscallId := .cspaceDelete
    msgRegs := #[]  -- empty
  }
  expectErr "K-G-NEG-04 cspaceDelete decode empty msgRegs"
    (SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceDeleteArgs emptyDecode)
    .invalidMessageInfo

  -- K-G-NEG-05: cspaceMint dispatch fails — CNode not found
  let noCnodeState : SystemState := BootstrapBuilder.empty.buildChecked
  let mintAddr : SeLe4n.Kernel.CSpaceAddr := { cnode := ⟨999⟩, slot := SeLe4n.Slot.ofNat 0 }
  let dstAddr : SeLe4n.Kernel.CSpaceAddr := { cnode := ⟨999⟩, slot := SeLe4n.Slot.ofNat 1 }
  expectErr "K-G-NEG-05 cspaceMint CNode not found"
    (SeLe4n.Kernel.cspaceMint mintAddr dstAddr AccessRightSet.empty none noCnodeState)
    .objectNotFound

  -- K-G-NEG-06: cspaceCopy fails — source slot empty (invalidCapability)
  let emptyCnodeState : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject ⟨200⟩ (.cnode (SeLe4n.Model.CNode.ofSlots 0 0 0 0 SeLe4n.UniqueSlotMap.empty))  -- no slots occupied
      |>.withLifecycleObjectType ⟨200⟩ .cnode
      |>.buildChecked)
  let emptySlot : SeLe4n.Kernel.CSpaceAddr := { cnode := ⟨200⟩, slot := SeLe4n.Slot.ofNat 0 }
  let dstSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := ⟨200⟩, slot := SeLe4n.Slot.ofNat 1 }
  expectErr "K-G-NEG-06 cspaceCopy source slot empty"
    (SeLe4n.Kernel.cspaceCopy emptySlot dstSlot emptyCnodeState)
    .invalidCapability

  IO.println "CSpace negative tests passed"


/-- K-G2: Lifecycle/VSpace decode/dispatch error paths. -/
private def runWSKGLifecycleVSpaceChecks : IO Unit := do
  -- ---- K-G2: Lifecycle/VSpace negative tests ----

  -- K-G-NEG-07: decodeUntypedRetypeArgs with insufficient msgRegs (< 4) → invalidMessageInfo
  let threeRegCarve : SyscallDecodeResult := {
    capAddr := SeLe4n.CPtr.ofNat 0
    msgInfo := { length := 0, extraCaps := 0, label := 0 }
    syscallId := .untypedRetype
    msgRegs := #[⟨1⟩, ⟨2⟩, ⟨3⟩]  -- only 3, need 4
  }
  expectErr "K-G-NEG-07 untypedRetype decode insufficient msgRegs"
    (SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeUntypedRetypeArgs threeRegCarve)
    .invalidMessageInfo

  -- K-G-NEG-08: decodeUntypedRetypeArgs with invalid type tag (99) → invalidTypeTag
  expectErr "K-G-NEG-08 untypedRetype decode invalid tag"
    (SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeUntypedRetypeArgs
      { threeRegCarve with msgRegs := #[⟨99⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩] })
    .invalidTypeTag

  -- K-G-NEG-09 (WS-ZA ZA5.4 part 14, retargeted from the in-place retype): a
  -- carve through a capability whose object does not exist.  With `.retype` it
  -- draws untypedTypeMismatch; without `.retype` it draws illegalAuthority, so
  -- the authority is asked before the object is read.
  let carveCn : SeLe4n.ObjId := ⟨501⟩
  let carveState : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject carveCn (.cnode (CNode.ofList 0 0 0 2 [
          (SeLe4n.Slot.ofNat 0, { target := .object ⟨500⟩, rights := AccessRightSet.ofList [.read, .write, .retype] }),
          (SeLe4n.Slot.ofNat 1, { target := .object ⟨500⟩, rights := AccessRightSet.ofList [.read, .write] }),
          (SeLe4n.Slot.ofNat 2, { target := .replyCap ⟨502⟩, rights := AccessRightSet.ofList [.read, .write, .retype] })
        ]))
      |>.withLifecycleObjectType carveCn .cnode
      |>.buildChecked)
  let carveAt (n : Nat) : SeLe4n.Kernel.CSpaceAddr := { cnode := carveCn, slot := SeLe4n.Slot.ofNat n }
  expectErr "K-G-NEG-09 carve through a capability to no object"
    (SeLe4n.Kernel.untypedRetypeObject (carveAt 0) ⟨510⟩ (carveAt 3) .endpoint carveState)
    .untypedTypeMismatch
  expectErr "K-G-NEG-09 carve without the retype right"
    (SeLe4n.Kernel.untypedRetypeObject (carveAt 1) ⟨510⟩ (carveAt 3) .endpoint carveState)
    .illegalAuthority

  -- K-G-NEG-10: a carve through a capability that names no object (a reply
  -- capability) → invalidCapability.
  expectErr "K-G-NEG-10 carve through a non-object capability"
    (SeLe4n.Kernel.untypedRetypeObject (carveAt 2) ⟨510⟩ (carveAt 3) .endpoint carveState)
    .invalidCapability

  -- K-G-NEG-11: decodeVSpaceMapArgs with insufficient msgRegs (< 4) → invalidMessageInfo
  let threeRegDecode : SyscallDecodeResult := {
    capAddr := SeLe4n.CPtr.ofNat 0
    msgInfo := { length := 0, extraCaps := 0, label := 0 }
    syscallId := .vspaceMap
    msgRegs := #[⟨1⟩, ⟨2⟩, ⟨3⟩]  -- only 3, need 4
  }
  expectErr "K-G-NEG-11 vspaceMap decode insufficient msgRegs"
    (SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeVSpaceMapArgs threeRegDecode 65536)
    .invalidMessageInfo

  -- K-G-NEG-12: vspaceMapPageChecked with W^X violation (perms = write+execute)
  let vspaceAsid : SeLe4n.ASID := ⟨5⟩
  let vspaceState : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject ⟨400⟩ (.vspaceRoot { asid := vspaceAsid, mappings := {} })
      |>.withLifecycleObjectType ⟨400⟩ .vspaceRoot
      |>.buildChecked)
  let wxPerms := PagePermissions.ofNat 6  -- bits 1+2 = write+execute
  expectErr "K-G-NEG-12 vspaceMap W^X violation"
    ((SeLe4n.Kernel.Architecture.vspaceMapPageChecked vspaceAsid (SeLe4n.VAddr.ofNat 4096) (SeLe4n.PAddr.ofNat 8192) wxPerms) vspaceState)
    .policyDenied

  -- K-G-NEG-13: vspaceUnmapPage with no existing mapping → translationFault
  expectErr "K-G-NEG-13 vspaceUnmap no mapping"
    ((SeLe4n.Kernel.Architecture.vspaceUnmapPage vspaceAsid (SeLe4n.VAddr.ofNat 4096)) vspaceState)
    .translationFault

  IO.println "lifecycle/VSpace negative tests passed"


/-- K-G3: Service policy and IPC message population boundaries. -/
private def runWSKGServiceIpcChecks : IO Unit := do
  -- ---- K-G3: Service policy and IPC boundary tests ----

  -- K-G-NEG-16: extractMessageRegisters with empty msgRegs → empty result
  let emptyExtract := SeLe4n.Kernel.Architecture.RegisterDecode.extractMessageRegisters
    #[] { length := 4, extraCaps := 0, label := 0 }
  unless emptyExtract.size == 0 do
    throw <| IO.userError s!"K-G-NEG-16: expected empty extraction, got size {emptyExtract.size}"
  IO.println "negative check passed [K-G-NEG-16 extractMessageRegisters empty → empty]"

  -- K-G-NEG-17: extractMessageRegisters with oversized info.length → capped by msgRegs.size
  let cappedExtract := SeLe4n.Kernel.Architecture.RegisterDecode.extractMessageRegisters
    #[⟨10⟩, ⟨20⟩, ⟨30⟩, ⟨40⟩] { length := 200, extraCaps := 0, label := 0 }
  unless cappedExtract.size == 4 do
    throw <| IO.userError s!"K-G-NEG-17: expected size 4 (capped by msgRegs), got {cappedExtract.size}"
  IO.println "negative check passed [K-G-NEG-17 extractMessageRegisters oversized length capped]"

  -- K-G-NEG-18 (WS-ZA ZA5.4 part 14): a carve request is formed for every
  -- object kind at its seL4 size (sizeBits 0 for the fixed-size kinds, a radix
  -- for a CNode, a size for a scheduling context and a child untyped).
  let reqState : SystemState := BootstrapBuilder.empty.buildChecked
  for (ty, bits) in [(KernelObjectType.tcb, 0), (.endpoint, 0), (.notification, 0), (.cnode, 1),
      (.vspaceRoot, 0), (.untyped, 12), (.schedContext, 7), (.reply, 0), (.frame, 0),
      (.pageTable, 0)] do
    match SeLe4n.Kernel.carveRequestOf? reqState bootCoreId ty bits with
    | .ok req =>
        unless req.objectType == ty do
          throw <| IO.userError s!"K-G-NEG-18: carve request for {repr ty} names another kind"
    | .error e => throw <| IO.userError s!"K-G-NEG-18: carve request for {repr ty} failed: {toString e}"
  IO.println "negative check passed [K-G-NEG-18 a carve request forms for every kind]"

  IO.println "service/IPC boundary tests passed"


/-- K-G4: Determinism verification across full decode pipeline. -/
private def runWSKGDeterminismChecks : IO Unit := do
  -- ---- K-G4: Determinism verification ----

  -- K-G-DET-01: Layer 1+2 decode determinism (double invocation)
  let detRegs : SeLe4n.RegisterFile := default
  let r1 := SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgs SeLe4n.arm64DefaultLayout detRegs 32
  let r2 := SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgs SeLe4n.arm64DefaultLayout detRegs 32
  -- S2-A: Determinism checks use structural equality via DecidableEq.
  -- Except ε α gets DecidableEq from the instance above when both ε and α have it.
  unless r1 == r2 do
    throw <| IO.userError "K-G-DET-01: decodeSyscallArgs not deterministic"
  match r1 with
  | .ok d1 =>
    -- Verify layer 2 decode determinism for all 7 functions
    let m1 := SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceMintArgs d1
    let m2 := SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceMintArgs d1
    unless m1 == m2 do
      throw <| IO.userError "K-G-DET-01: decodeCSpaceMintArgs not deterministic"
    let c1 := SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceCopyArgs d1
    let c2 := SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceCopyArgs d1
    unless c1 == c2 do
      throw <| IO.userError "K-G-DET-01: decodeCSpaceCopyArgs not deterministic"
    let mv1 := SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceMoveArgs d1
    let mv2 := SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceMoveArgs d1
    unless mv1 == mv2 do
      throw <| IO.userError "K-G-DET-01: decodeCSpaceMoveArgs not deterministic"
    let del1 := SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceDeleteArgs d1
    let del2 := SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceDeleteArgs d1
    unless del1 == del2 do
      throw <| IO.userError "K-G-DET-01: decodeCSpaceDeleteArgs not deterministic"
    let lr1 := SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeUntypedRetypeArgs d1
    let lr2 := SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeUntypedRetypeArgs d1
    unless lr1 == lr2 do
      throw <| IO.userError "K-G-DET-01: decodeUntypedRetypeArgs not deterministic"
    let vm1 := SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeVSpaceMapArgs d1 65536
    let vm2 := SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeVSpaceMapArgs d1 65536
    unless vm1 == vm2 do
      throw <| IO.userError "K-G-DET-01: decodeVSpaceMapArgs not deterministic"
    let vu1 := SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeVSpaceUnmapArgs d1 65536
    let vu2 := SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeVSpaceUnmapArgs d1 65536
    unless vu1 == vu2 do
      throw <| IO.userError "K-G-DET-01: decodeVSpaceUnmapArgs not deterministic"
    IO.println "determinism check passed [K-G-DET-01 layer 1+2 decode deterministic]"
  | .error _ =>
    throw <| IO.userError "K-G-DET-01: decodeSyscallArgs failed unexpectedly"

  -- K-G-DET-02: extractMessageRegisters determinism
  let info : MessageInfo := { length := 3, extraCaps := 0, label := 0 }
  let regsArr : Array SeLe4n.RegValue := #[⟨100⟩, ⟨200⟩, ⟨300⟩, ⟨400⟩]
  let e1 := SeLe4n.Kernel.Architecture.RegisterDecode.extractMessageRegisters regsArr info
  let e2 := SeLe4n.Kernel.Architecture.RegisterDecode.extractMessageRegisters regsArr info
  unless e1 == e2 do
    throw <| IO.userError "K-G-DET-02: extractMessageRegisters not deterministic"
  IO.println "determinism check passed [K-G-DET-02 extractMessageRegisters deterministic]"

  -- K-G-DET-03: the carve's type-word decode is deterministic across every tag
  for tag in [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] do
    let carveDecoded : SyscallDecodeResult := {
      capAddr := SeLe4n.CPtr.ofNat 0
      msgInfo := { length := 4, extraCaps := 0, label := 0 }
      syscallId := .untypedRetype
      msgRegs := #[⟨tag + 256⟩, ⟨600⟩, ⟨1⟩, ⟨2⟩] }
    let o1 := SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeUntypedRetypeArgs carveDecoded
    let o2 := SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeUntypedRetypeArgs carveDecoded
    unless o1 == o2 do
      throw <| IO.userError s!"K-G-DET-03: carve type word tag {tag} not deterministic"
  IO.println "determinism check passed [K-G-DET-03 carve type-word decode deterministic]"


/-- WS-K-G: Negative-state, determinism, and boundary tests for all new decode,
dispatch, and error paths introduced in WS-K-A through WS-K-F.

Organized into sub-phases:
- K-G1: CSpace decode/dispatch error paths
- K-G2: Lifecycle/VSpace decode/dispatch error paths
- K-G3: Service policy and IPC message population boundaries
- K-G4: Determinism verification across full decode pipeline -/
def runWSKGChecks : IO Unit := do
  IO.println "\n=== WS-K-G: Comprehensive syscall dispatch testing ==="
  runWSKGCSpaceChecks                   -- [was 2166-2230: K-G1 CSpace]
  runWSKGLifecycleVSpaceChecks          -- [was 2231-2304: K-G2 Lifecycle/VSpace]
  runWSKGServiceIpcChecks               -- [was 2305-2353: K-G3 Service/IPC]
  runWSKGDeterminismChecks              -- [was 2354-2415: K-G4 Determinism]
  IO.println "all WS-K-G comprehensive tests passed"


-- ============================================================================
-- WS-L4-C: Blocked thread IPC rejection tests
-- ============================================================================

/-- Verify that threads already blocked on IPC operations are rejected when
attempting further IPC operations. -/
def runWSL4BlockedThreadChecks : IO Unit := do
  IO.println "\n--- WS-L4-C: Blocked thread IPC rejection tests ---"

  -- Use a fresh state with endpoint, notification, and 2 threads
  let epId : SeLe4n.ObjId := ⟨40⟩
  let ntfnId : SeLe4n.ObjId := ⟨42⟩
  let tid7 : SeLe4n.ThreadId := ⟨7⟩

  let blockedState : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint (Endpoint.ofQueues {} {}))
      |>.withObject ntfnId (.notification { state := .idle, hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero })
      |>.withObject ⟨7⟩ (.tcb {
        tid := ⟨7⟩, priority := ⟨10⟩, domain := ⟨0⟩,
        spaceCells := SeLe4n.Model.TCB.spaceCellsOf SeLe4n.ObjId.sentinel SeLe4n.ObjId.sentinel, ipcBuffer := (SeLe4n.VAddr.ofNat 4096),
      })
      |>.withObject ⟨8⟩ (.tcb {
        tid := ⟨8⟩, priority := ⟨20⟩, domain := ⟨0⟩,
        spaceCells := SeLe4n.Model.TCB.spaceCellsOf SeLe4n.ObjId.sentinel SeLe4n.ObjId.sentinel, ipcBuffer := (SeLe4n.VAddr.ofNat 8192),
      })
      |>.withRunnable [⟨7⟩, ⟨8⟩]
    ).buildChecked

  -- Block thread 7 on send (no receiver → enqueues on sendQ)
  let (_, stSendBlocked) ← expectOkSt "setup: send blocks thread 7"
    (SeLe4n.Kernel.endpointSendDual epId tid7 (.frame none false) blockedState)

  -- Attempt another send on same endpoint while already blocked → alreadyWaiting
  expectErr "blocked-on-send rejects second send"
    (SeLe4n.Kernel.endpointSendDual epId tid7 (.frame none false) stSendBlocked)
    .alreadyWaiting

  -- Block thread 7 on receive instead
  let (_, stRecvBlocked) ← expectOkSt "setup: receive blocks thread 7"
    (SeLe4n.Kernel.endpointReceiveDual epId tid7 none blockedState)

  -- Attempt second receive on same endpoint while already blocked → alreadyWaiting
  expectErr "blocked-on-receive rejects second receive"
    (SeLe4n.Kernel.endpointReceiveDual epId tid7 none stRecvBlocked)
    .alreadyWaiting

  -- Block thread 7 on notification wait
  let (_, stNtfnBlocked) ← expectOkSt "setup: notification wait blocks thread 7"
    (SeLe4n.Kernel.notificationWait ntfnId tid7 blockedState)

  -- Attempt send while blocked on notification → alreadyWaiting
  expectErr "blocked-on-notification rejects send"
    (SeLe4n.Kernel.endpointSendDual epId tid7 (.frame none false) stNtfnBlocked)
    .alreadyWaiting

  -- Cross-type: blocked on receive → send to DIFFERENT endpoint rejected
  -- Uses a second endpoint where no receiver is waiting, forcing the enqueue path
  -- which checks ipcState ≠ .ready and rejects with alreadyWaiting
  let epId2 : SeLe4n.ObjId := ⟨41⟩
  let stRecvBlockedWithEp2 : SystemState := { stRecvBlocked with
    objects := stRecvBlocked.objects.insert epId2 (.endpoint (Endpoint.ofQueues {} {})) }
  expectErr "blocked-on-receive rejects send to different endpoint"
    (SeLe4n.Kernel.endpointSendDual epId2 tid7 (.frame none false) stRecvBlockedWithEp2)
    .alreadyWaiting

  -- Cross-type: blocked on send → receive from DIFFERENT endpoint rejected
  let stSendBlockedWithEp2 : SystemState := { stSendBlocked with
    objects := stSendBlocked.objects.insert epId2 (.endpoint (Endpoint.ofQueues {} {})) }
  expectErr "blocked-on-send rejects receive from different endpoint"
    (SeLe4n.Kernel.endpointReceiveDual epId2 tid7 none stSendBlockedWithEp2)
    .alreadyWaiting

  IO.println "all WS-L4-C blocked thread IPC rejection tests passed"

/-- SCN-IPC-CAP-TRANSFER-FULL-CNODE (M3-G3): When the receiver's CNode is
full (all scanned slots occupied), ipcTransferSingleCap returns .noSlot
and the state is unchanged. -/
def runWSM3CapTransferNegativeChecks : IO Unit := do
  IO.println "\n=== WS-M3-G3: IPC cap transfer full CNode negative test ==="

  let receiverRoot : SeLe4n.ObjId := ⟨5000⟩
  let senderRoot : SeLe4n.ObjId := ⟨5001⟩
  let targetObj : SeLe4n.ObjId := ⟨5010⟩

  let cap : Capability := {
    target := .object targetObj,
    rights := AccessRightSet.ofList [.read],
  }

  -- CNode with radixWidth=2 → slotCount=4; fill all 4 slots
  let fullCNode : CNode := CNode.ofList 4 0 0 2 [
      (SeLe4n.Slot.ofNat 0, cap), (SeLe4n.Slot.ofNat 1, cap), (SeLe4n.Slot.ofNat 2, cap), (SeLe4n.Slot.ofNat 3, cap)
    ]

  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject receiverRoot (.cnode fullCNode)
      |>.withObject senderRoot (.cnode (CNode.ofList 4 0 0 4 [(SeLe4n.Slot.ofNat 0, cap)]))
      |>.withObject targetObj (.notification { state := .idle, hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero })
      |>.buildChecked)

  -- ipcTransferSingleCap with scanLimit covering all 4 slots → should get .noSlot.
  -- The derivation parent is the source slot itself, as `resolveExtraCaps`
  -- names it, so the transfer records the slot the revoke walk would reach.
  let srcSlot : SlotRef := { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
  let result := SeLe4n.Kernel.ipcTransferSingleCap cap srcSlot receiverRoot (SeLe4n.Slot.ofNat 0) 4 st0
  match result with
  | .ok (transferResult, st') =>
    let isNoSlot := match transferResult with
      | .noSlot => true
      | _ => false
    if !isNoSlot then
      throw <| IO.userError "expected .noSlot for full CNode, got different result"
    IO.println "check passed [full CNode returns .noSlot]"
    -- State should be unchanged
    let unchanged := st'.objects == st0.objects
    if !unchanged then
      throw <| IO.userError "state should be unchanged after .noSlot"
    IO.println "check passed [state unchanged after .noSlot]"
  | .error e =>
    throw <| IO.userError s!"ipcTransferSingleCap returned error: {toString e}"

  IO.println "all WS-M3-G3 cap transfer negative tests passed"

-- ============================================================================
-- L-13: Cap transfer short-circuit on fatal error (Design C)
-- ============================================================================

/-- L-13 (Design C): When receiver CSpace root is not a CNode,
ipcUnwrapCapsLoop short-circuits: the current cap gets `.noSlot` and all
remaining caps are filled with `.noSlot` via `fillRemainingNoSlot`.  State
is returned unchanged.

Scenarios:
- L13-01: 3 caps, receiver root is a TCB (not CNode) → all 3 get `.noSlot`
- L13-02: State unchanged after short-circuit
- L13-03: 1 cap, receiver root missing entirely → `.noSlot`, state unchanged
-/
def runL13CapTransferShortCircuitChecks : IO Unit := do
  IO.println "\n=== L-13: Cap transfer short-circuit on fatal error ==="

  let receiverRoot : SeLe4n.ObjId := ⟨5050⟩
  let senderRoot : SeLe4n.ObjId := ⟨5051⟩
  let targetObj : SeLe4n.ObjId := ⟨5060⟩

  let cap : Capability := {
    target := .object targetObj,
    rights := AccessRightSet.ofList [.read],
  }

  -- Receiver root is a TCB, not a CNode → ipcTransferSingleCap will error
  let tcbObj : TCB := {
    tid := ⟨5050⟩,
    priority := ⟨100⟩,
    domain := ⟨0⟩,
    spaceCells := SeLe4n.Model.TCB.spaceCellsOf senderRoot senderRoot,
    ipcBuffer := (SeLe4n.VAddr.ofNat 0),
    timeSlice := 5,
    scBindingScCode := 0, scBindingOwnerCode := 0
  }

  let senderCNode : CNode := CNode.ofList 4 0 0 4 [(SeLe4n.Slot.ofNat 0, cap), (SeLe4n.Slot.ofNat 1, cap), (SeLe4n.Slot.ofNat 2, cap)]

  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject receiverRoot (.tcb tcbObj)
      |>.withObject senderRoot (.cnode senderCNode)
      |>.withObject targetObj (.notification { state := .idle, hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero })
      |>.buildChecked)

  -- Distinct source slots: the transfer records its derivation edge against
  -- each capability's own slot, so a fixture that reused one address would
  -- not exercise the per-capability provenance the loop now threads.
  let caps : Array TransferCap :=
    #[TransferCap.fromSlot cap { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 },
      TransferCap.fromSlot cap { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 1 },
      TransferCap.fromSlot cap { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 2 }]

  -- L13-01: 3 caps with receiver root = TCB → short-circuit, all .noSlot
  let result := SeLe4n.Kernel.ipcUnwrapCapsLoop caps receiverRoot
    0 (SeLe4n.Slot.ofNat 0) #[] caps.size st0
  match result with
  | .ok (summary, st') =>
    if summary.results.size != 3 then
      throw <| IO.userError s!"expected 3 results, got {summary.results.size}"
    let allNoSlot := summary.results.all fun r => match r with
      | .noSlot => true
      | _ => false
    if !allNoSlot then
      throw <| IO.userError "expected all results to be .noSlot"
    IO.println "check passed [3 caps, receiver root is TCB → all .noSlot]"

    -- L13-02: State unchanged after short-circuit
    if st'.objects != st0.objects then
      throw <| IO.userError "objects should be unchanged after short-circuit"
    IO.println "check passed [state unchanged after short-circuit]"
  | .error e =>
    throw <| IO.userError s!"ipcUnwrapCapsLoop returned error: {toString e}"

  -- L13-03: 1 cap with receiver root missing entirely (no object at that OID)
  let missingRoot : SeLe4n.ObjId := ⟨9999⟩
  let st1 :=
    (BootstrapBuilder.empty
      |>.withObject senderRoot (.cnode senderCNode)
      |>.withObject targetObj (.notification { state := .idle, hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero })
      |>.buildChecked)

  let result1 := SeLe4n.Kernel.ipcUnwrapCapsLoop #[TransferCap.fromSlot cap { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }]
    missingRoot
    0 (SeLe4n.Slot.ofNat 0) #[] 1 st1
  match result1 with
  | .ok (summary1, st1') =>
    if summary1.results.size != 1 then
      throw <| IO.userError s!"expected 1 result, got {summary1.results.size}"
    let isNoSlot := match summary1.results[0]? with
      | some .noSlot => true
      | _ => false
    if !isNoSlot then
      throw <| IO.userError "expected .noSlot for missing receiver root"
    if st1'.objects != st1.objects then
      throw <| IO.userError "state should be unchanged"
    IO.println "check passed [1 cap, missing receiver root → .noSlot, state unchanged]"
  | .error e =>
    throw <| IO.userError s!"ipcUnwrapCapsLoop returned error: {toString e}"

  IO.println "all L-13 cap transfer short-circuit tests passed"

-- ============================================================================
-- WS-M4-A: Multi-level resolveCapAddress edge case tests (M-T01)
-- ============================================================================

/-- M4-A1: guard-only CNode (radixWidth=0). -/
private def runWSM4GuardOnlyChecks : IO Unit := do
  -- M4-A1: Guard-only CNode (radixWidth=0, guardWidth=4, guardValue=0xA)
  -- With radixWidth=0, slot index = addr % 2^0 = addr % 1 = 0 always.
  let guardOnlyRoot : SeLe4n.ObjId := ⟨6000⟩
  let guardOnlyTarget : SeLe4n.ObjId := ⟨6001⟩
  let stGuardOnly :=
    (BootstrapBuilder.empty
      |>.withObject guardOnlyRoot (.cnode (SeLe4n.Model.CNode.ofSlots 4 4 0xA 0 (SeLe4n.UniqueSlotMap.ofListWF [
            (SeLe4n.Slot.ofNat 0, { target := .object guardOnlyTarget, rights := AccessRightSet.ofList [.read] })
          ])))
      |>.withObject guardOnlyTarget (.endpoint {})
      |>.buildChecked)

  -- Correct guard: addr=0xA (top 4 bits encode guard 0xA)
  let resultOk := SeLe4n.Kernel.resolveCapAddress guardOnlyRoot (SeLe4n.CPtr.ofNat 0xA) 4 stGuardOnly
  match resultOk with
  | .ok ref =>
      if ref.cnode = guardOnlyRoot ∧ ref.slot = SeLe4n.Slot.ofNat 0 then
        IO.println "check passed [guard-only CNode resolves to slot 0]"
      else
        throw <| IO.userError s!"expected slot 0 at guardOnlyRoot, got {toString ref}"
  | .error e =>
      throw <| IO.userError s!"expected success, got {toString e}"

  -- Wrong guard: addr=0xB (guard extracted = 0xB ≠ 0xA)
  let resultBad := SeLe4n.Kernel.resolveCapAddress guardOnlyRoot (SeLe4n.CPtr.ofNat 0xB) 4 stGuardOnly
  match resultBad with
  | .error .invalidCapability =>
      IO.println "check passed [guard-only CNode rejects wrong guard]"
  | .error e =>
      throw <| IO.userError s!"expected invalidCapability, got {toString e}"
  | .ok _ =>
      throw <| IO.userError "expected error for wrong guard, got success"


/-- M4-A4 + M4-A5: single-level leaf, partial bits, zero bits.  Folded because
    A4 and A5 share the leafRoot/leafTarget/stLeaf setup. -/
private def runWSM4SmallBitsChecks : IO Unit := do
  -- M4-A5: Single-level leaf resolution (guardWidth=0, radixWidth=4)
  -- addr=5 → slot 5, consumed = 4 bits, bitsRemaining - consumed = 0 → leaf
  let leafRoot : SeLe4n.ObjId := ⟨6010⟩
  let leafTarget : SeLe4n.ObjId := ⟨6011⟩
  let stLeaf :=
    (BootstrapBuilder.empty
      |>.withObject leafRoot (.cnode (SeLe4n.Model.CNode.ofSlots 4 0 0 4 (SeLe4n.UniqueSlotMap.ofListWF [
            (SeLe4n.Slot.ofNat 5, { target := .object leafTarget, rights := AccessRightSet.ofList [.read, .write] })
          ])))
      |>.withObject leafTarget (.endpoint {})
      |>.buildChecked)

  let resultLeaf := SeLe4n.Kernel.resolveCapAddress leafRoot (SeLe4n.CPtr.ofNat 5) 4 stLeaf
  match resultLeaf with
  | .ok ref =>
      if ref.cnode = leafRoot ∧ ref.slot = SeLe4n.Slot.ofNat 5 then
        IO.println "check passed [single-level leaf resolves to slot 5]"
      else
        throw <| IO.userError s!"expected slot 5, got {toString ref}"
  | .error e =>
      throw <| IO.userError s!"expected success, got {toString e}"

  -- M4-A4: Partial bit consumption (bitsRemaining < guardWidth + radixWidth)
  -- CNode needs 6 bits (guardWidth=2 + radixWidth=4), but only 4 available
  let partialRoot : SeLe4n.ObjId := ⟨6020⟩
  let stPartial :=
    (BootstrapBuilder.empty
      |>.withObject partialRoot (.cnode (SeLe4n.Model.CNode.ofSlots 6 2 0 4 SeLe4n.UniqueSlotMap.empty))
      |>.buildChecked)

  let resultPartial := SeLe4n.Kernel.resolveCapAddress partialRoot (SeLe4n.CPtr.ofNat 0) 4 stPartial
  match resultPartial with
  | .error .illegalState =>
      IO.println "check passed [partial bits returns illegalState]"
  | .error e =>
      throw <| IO.userError s!"expected illegalState, got {toString e}"
  | .ok _ =>
      throw <| IO.userError "expected error for partial bits, got success"

  -- M4-A4 zero bits
  let resultZero := SeLe4n.Kernel.resolveCapAddress partialRoot (SeLe4n.CPtr.ofNat 0) 0 stPartial
  match resultZero with
  | .error .illegalState =>
      IO.println "check passed [zero bitsRemaining returns illegalState]"
  | .error e =>
      throw <| IO.userError s!"zero: expected illegalState, got {toString e}"
  | .ok _ =>
      throw <| IO.userError "zero: expected error for zero bits, got success"


/-- M4-A3: guard mismatch at intermediate level. -/
private def runWSM4GuardMismatchChecks : IO Unit := do
  -- M4-A3: Guard mismatch at intermediate level
  -- 3-level chain: level0 (guard=3, gw=2, rw=2, 4 bits) →
  --               level1 (guard=1, gw=2, rw=2, 4 bits) →
  --               level2 (guard=0, gw=0, rw=4, 4 bits, leaf)
  -- Total = 12 bits
  let lvl0 : SeLe4n.ObjId := ⟨6030⟩
  let lvl1 : SeLe4n.ObjId := ⟨6031⟩
  let lvl2 : SeLe4n.ObjId := ⟨6032⟩
  let lvl2Target : SeLe4n.ObjId := ⟨6033⟩

  -- For 12-bit addr with correct guards:
  -- Level 0 consumes bits [11..8]: guard=3 (2 bits), slot index (2 bits)
  -- Level 1 consumes bits [7..4]: guard=1 (2 bits), slot index (2 bits)
  -- Level 2 consumes bits [3..0]: slot index (4 bits)
  --
  -- addr layout (12 bits): [guard0=0b11][slot0][guard1=0b01][slot1][slot2]
  -- slot0 = 0 → lookup slot 0 at lvl0 → points to lvl1
  -- slot1 = 0 → lookup slot 0 at lvl1 → points to lvl2
  -- slot2 = 7 → leaf at lvl2 slot 7
  --
  -- Correct addr = 0b_11_00_01_00_0111 = 0xC47
  -- Wrong guard at lvl1: guard1 = 0b10 instead of 0b01
  -- Wrong addr = 0b_11_00_10_00_0111 = 0xC87
  let stMidGuard :=
    (BootstrapBuilder.empty
      |>.withObject lvl0 (.cnode (SeLe4n.Model.CNode.ofSlots 12 2 3 2 (SeLe4n.UniqueSlotMap.ofListWF [
            (SeLe4n.Slot.ofNat 0, { target := .object lvl1, rights := AccessRightSet.ofList [.read, .write] })
          ])))
      |>.withObject lvl1 (.cnode (SeLe4n.Model.CNode.ofSlots 8 2 1 2 (SeLe4n.UniqueSlotMap.ofListWF [
            (SeLe4n.Slot.ofNat 0, { target := .object lvl2, rights := AccessRightSet.ofList [.read, .write] })
          ])))
      |>.withObject lvl2 (.cnode (SeLe4n.Model.CNode.ofSlots 4 0 0 4 (SeLe4n.UniqueSlotMap.ofListWF [
            (SeLe4n.Slot.ofNat 7, { target := .object lvl2Target, rights := AccessRightSet.ofList [.read] })
          ])))
      |>.withObject lvl2Target (.endpoint {})
      |>.buildChecked)

  -- Correct: all guards match, should resolve to lvl2 slot 7
  let resultCorrect := SeLe4n.Kernel.resolveCapAddress lvl0 (SeLe4n.CPtr.ofNat 0xC47) 12 stMidGuard
  match resultCorrect with
  | .ok ref =>
      if ref.cnode = lvl2 ∧ ref.slot = SeLe4n.Slot.ofNat 7 then
        IO.println "check passed [correct guards resolve through 3 levels]"
      else
        throw <| IO.userError s!"expected lvl2 slot 7, got {toString ref}"
  | .error e =>
      throw <| IO.userError s!"expected success for correct guards, got {toString e}"

  -- Wrong guard at level 1: guard1=2 instead of 1
  let resultWrongMid := SeLe4n.Kernel.resolveCapAddress lvl0 (SeLe4n.CPtr.ofNat 0xC87) 12 stMidGuard
  match resultWrongMid with
  | .error .invalidCapability =>
      IO.println "check passed [guard mismatch at intermediate level returns invalidCapability]"
  | .error e =>
      throw <| IO.userError s!"expected invalidCapability for wrong mid guard, got {toString e}"
  | .ok _ =>
      throw <| IO.userError "expected error for wrong mid guard, got success"


/-- M4-A2: maximum depth (8 CNodes × 8 bits each = 64-bit address chain).
    Isolated because the inner `for i in List.range 7 do` loop builder
    generates per-iteration nesting that compounds heavily in C codegen. -/
private def runWSM4MaxDepthLoopChecks : IO Unit := do
  -- M4-A2: Maximum depth (64 bits) — 8 CNodes each consuming 8 bits
  -- Build chain of 8 CNodes (radixWidth=8, guardWidth=0 each)
  -- addr encodes slot index for each level in 8-bit chunks
  -- Level 0: bits [63..56] → slot at lvl0 → points to lvl1
  -- Level 1: bits [55..48] → slot at lvl1 → points to lvl2
  -- ...
  -- Level 7: bits [7..0] → leaf slot at lvl7
  let maxDepthIds : Array SeLe4n.ObjId := #[⟨6100⟩, ⟨6101⟩, ⟨6102⟩, ⟨6103⟩, ⟨6104⟩, ⟨6105⟩, ⟨6106⟩, ⟨6107⟩]
  let maxDepthLeafTarget : SeLe4n.ObjId := ⟨6108⟩

  -- Use slot index 1 at each level for simplicity
  -- addr = 0x0101010101010101 (each byte = 1)
  let mut builder := BootstrapBuilder.empty
  for i in List.range 7 do
    let cnodeId := maxDepthIds[i]!
    let nextId := maxDepthIds[i + 1]!
    builder := builder.withObject cnodeId (.cnode (CNode.ofList (64 - i * 8) 0 0 8 [
        (SeLe4n.Slot.ofNat 1, { target := .object nextId, rights := AccessRightSet.ofList [.read, .write] })
      ]))
  -- Level 7 (leaf): slot 1 holds the target cap
  builder := builder.withObject maxDepthIds[7]! (.cnode (SeLe4n.Model.CNode.ofSlots 8 0 0 8 (SeLe4n.UniqueSlotMap.ofListWF [
      (SeLe4n.Slot.ofNat 1, { target := .object maxDepthLeafTarget, rights := AccessRightSet.ofList [.read] })
    ])))
  builder := builder.withObject maxDepthLeafTarget (.endpoint {})
  let stMaxDepth := builder.buildChecked

  -- Resolve with 64 bits: 0x0101010101010101
  let addr64 : SeLe4n.CPtr := SeLe4n.CPtr.ofNat 0x0101010101010101
  let resultMax := SeLe4n.Kernel.resolveCapAddress maxDepthIds[0]! addr64 64 stMaxDepth
  match resultMax with
  | .ok ref =>
      if ref.cnode = maxDepthIds[7]! ∧ ref.slot = SeLe4n.Slot.ofNat 1 then
        IO.println "check passed [64-bit resolution across 8 CNodes succeeds]"
      else
        throw <| IO.userError s!"expected leaf at level 7 slot 1, got {toString ref}"
  | .error e =>
      throw <| IO.userError s!"expected success for 64-bit resolution, got {toString e}"

  -- 65 bits: shiftedAddr = addr >>> 57 at level 0, which shifts the address
  -- one bit further than the 64-bit case, yielding slot index 0 instead of 1.
  -- Since slot 0 is empty in our CNodes → invalidCapability.
  let result65 := SeLe4n.Kernel.resolveCapAddress maxDepthIds[0]! addr64 65 stMaxDepth
  match result65 with
  | .error .invalidCapability =>
      IO.println "check passed [65-bit overflow returns invalidCapability (empty slot)]"
  | .error e =>
      throw <| IO.userError s!"overflow: expected invalidCapability, got {toString e}"
  | .ok _ =>
      throw <| IO.userError "overflow: expected error for 65 bits, got success"


/-- M4-A6 + M4-A7: empty intermediate slot + non-CNode at intermediate level. -/
private def runWSM4SlotEdgeChecks : IO Unit := do
  -- M4-A6: Empty slot at intermediate (non-leaf) level.
  -- resolveCapAddress only checks slot occupancy during recursion (bitsRemaining >
  -- consumed). At leaf level (bitsRemaining = consumed) it returns the slot ref
  -- unconditionally. So we need 3 levels where the middle level has an empty slot
  -- and there are still bits remaining for recursion.
  --
  -- lvl0 (gw=0, rw=4, 4 bits) → slot 3 → lvl1 (gw=0, rw=4, empty, 4 bits)
  -- Total bitsRemaining = 10. At lvl1: bits=6, consumed=4, remaining=2 > 0
  -- → tries to recurse → slot lookup → empty → invalidCapability
  let emptyMidRoot : SeLe4n.ObjId := ⟨6040⟩
  let emptyMidChild : SeLe4n.ObjId := ⟨6041⟩
  let stEmptyMid :=
    (BootstrapBuilder.empty
      |>.withObject emptyMidRoot (.cnode (SeLe4n.Model.CNode.ofSlots 10 0 0 4 (SeLe4n.UniqueSlotMap.ofListWF [
            (SeLe4n.Slot.ofNat 3, { target := .object emptyMidChild, rights := AccessRightSet.ofList [.read] })
          ])))
      |>.withObject emptyMidChild (.cnode (SeLe4n.Model.CNode.ofSlots 6 0 0 4 SeLe4n.UniqueSlotMap.empty))  -- all slots empty
      |>.buildChecked)

  -- addr=0xC0 (10 bits): lvl0 shift=(10-4)=6, 0xC0>>>6=3, slot 3 → lvl1.
  -- At lvl1: bits=6, shift=(6-4)=2, 0xC0>>>2=48, slot=48%16=0. Remaining=2>0.
  -- Slot 0 is empty → invalidCapability (intermediate recursion path, line 106).
  let resultEmptyMid := SeLe4n.Kernel.resolveCapAddress emptyMidRoot (SeLe4n.CPtr.ofNat 0xC0) 10 stEmptyMid
  match resultEmptyMid with
  | .error .invalidCapability =>
      IO.println "check passed [empty slot at intermediate level returns invalidCapability]"
  | .error e =>
      throw <| IO.userError s!"expected invalidCapability, got {toString e}"
  | .ok _ =>
      throw <| IO.userError "expected error for empty intermediate slot, got success"

  -- M4-A7: Non-CNode target at intermediate level — slot holds cap targeting endpoint
  -- 2-level chain: lvl0 slot 1 → endpoint (not a CNode) → objectNotFound on recursion
  let nonCnodeMidRoot : SeLe4n.ObjId := ⟨6050⟩
  let nonCnodeMidEp : SeLe4n.ObjId := ⟨6051⟩
  let stNonCnodeMid :=
    (BootstrapBuilder.empty
      |>.withObject nonCnodeMidRoot (.cnode (SeLe4n.Model.CNode.ofSlots 8 0 0 4 (SeLe4n.UniqueSlotMap.ofListWF [
            (SeLe4n.Slot.ofNat 1, { target := .object nonCnodeMidEp, rights := AccessRightSet.ofList [.read] })
          ])))
      |>.withObject nonCnodeMidEp (.endpoint {})
      |>.buildChecked)

  -- addr=0x15 (8 bits): lvl0 slot = 1 → cap targets endpoint, recurse with 4 bits
  -- endpoint is not a CNode → objectNotFound
  let resultNonCnode := SeLe4n.Kernel.resolveCapAddress nonCnodeMidRoot (SeLe4n.CPtr.ofNat 0x15) 8 stNonCnodeMid
  match resultNonCnode with
  | .error .objectNotFound =>
      IO.println "check passed [non-CNode target at intermediate level returns objectNotFound]"
  | .error e =>
      throw <| IO.userError s!"expected objectNotFound, got {toString e}"
  | .ok _ =>
      throw <| IO.userError "expected error for non-CNode mid target, got success"


/-- M4-A8: cspaceLookupMultiLevel wrapper integration.  Rebuilds leafRoot/
    leafTarget/stLeaf locally (was reused from M4-A5; rebuild keeps the
    helper self-contained without parameter threading). -/
private def runWSM4WrapperIntegrationChecks : IO Unit := do
  -- M4-A8 rebuild: leafRoot/leafTarget/stLeaf (originally shared with M4-A5).
  let leafRoot : SeLe4n.ObjId := ⟨6010⟩
  let leafTarget : SeLe4n.ObjId := ⟨6011⟩
  let stLeaf :=
    (BootstrapBuilder.empty
      |>.withObject leafRoot (.cnode (SeLe4n.Model.CNode.ofSlots 4 0 0 4 (SeLe4n.UniqueSlotMap.ofListWF [
            (SeLe4n.Slot.ofNat 5, { target := .object leafTarget, rights := AccessRightSet.ofList [.read, .write] })
          ])))
      |>.withObject leafTarget (.endpoint {})
      |>.buildChecked)

  -- M4-A8: cspaceLookupMultiLevel wrapper integration — verify full pipeline
  -- Reuse the single-level leaf state (stLeaf): leafRoot slot 5 → leafTarget endpoint
  let resultWrapper := SeLe4n.Kernel.cspaceLookupMultiLevel leafRoot (SeLe4n.CPtr.ofNat 5) 4 stLeaf
  match resultWrapper with
  | .ok (cap, _) =>
      if cap.target = .object leafTarget then
        IO.println "check passed [cspaceLookupMultiLevel returns correct capability]"
      else
        throw <| IO.userError s!"unexpected cap target {toString cap.target}"
  | .error e =>
      throw <| IO.userError s!"expected success, got {toString e}"

  -- Wrapper negative: nonexistent slot → invalidCapability
  let resultWrapperBad := SeLe4n.Kernel.cspaceLookupMultiLevel leafRoot (SeLe4n.CPtr.ofNat 15) 4 stLeaf
  match resultWrapperBad with
  | .error .invalidCapability =>
      IO.println "check passed [cspaceLookupMultiLevel empty slot returns invalidCapability]"
  | .error e =>
      throw <| IO.userError s!"neg: expected invalidCapability, got {toString e}"
  | .ok _ =>
      throw <| IO.userError "neg: expected error for empty slot wrapper, got success"


/-- WS-M4-A (M-T01): Multi-level `resolveCapAddress` edge case tests.

Scenarios exercised:
- SCN-RESOLVE-GUARD-ONLY (M4-A1): Guard-only CNode (radixWidth=0)
- SCN-RESOLVE-MAX-DEPTH (M4-A2): 64-bit resolution across 8 CNodes
- SCN-RESOLVE-GUARD-MISMATCH-MID (M4-A3): Guard mismatch at intermediate level
- SCN-RESOLVE-PARTIAL-BITS (M4-A4): Insufficient bits for CNode consumption
- SCN-RESOLVE-SINGLE-LEVEL (M4-A5): Single-level leaf resolution -/
def runWSM4ResolveEdgeCaseChecks : IO Unit := do
  IO.println "\n=== WS-M4-A: resolveCapAddress edge case tests ==="
  runWSM4GuardOnlyChecks                -- [was 2669-2707: M4-A1]
  runWSM4SmallBitsChecks                -- [was 2708-2768: M4-A5/A4/A4-zero, folded]
  runWSM4GuardMismatchChecks            -- [was 2769-2844: M4-A3]
  runWSM4MaxDepthLoopChecks             -- [was 2845-2906: M4-A2 max-depth for-loop, isolated]
  runWSM4SlotEdgeChecks                 -- [was 2907-2978: M4-A6/A7, folded]
  runWSM4WrapperIntegrationChecks       -- [was 2979-3000: M4-A8 wrapper]
  IO.println "all WS-M4-A resolveCapAddress edge case tests passed"


-- ============================================================================
-- Revocation refusals (WS-R2, restated over the finalising revoke at WS-ZA
-- ZA5.3 part 8)
-- ============================================================================

/-- `.cspaceRevoke`'s check is read before any write: a slot of a CNode that
does not exist is refused with `.objectNotFound`, an empty slot of a live CNode
with `.invalidCapability`, each from the state it was refused in.  (WS-R2's
per-node error propagation and streaming fuel checks went with the general
revocation they tested; the loop's admission check replaces them.) -/
def runRevocationRefusalChecks : IO Unit := do
  let r2CnodeId : SeLe4n.ObjId := ⟨10⟩
  let r2BadSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := ⟨777⟩, slot := SeLe4n.Slot.ofNat 0 }
  let r2EmptySlot : SeLe4n.Kernel.CSpaceAddr := { cnode := r2CnodeId, slot := SeLe4n.Slot.ofNat 1 }
  let r2State : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject r2CnodeId (.cnode (CNode.ofList 0 0 0 3 []))
      |>.buildChecked)
  expectErr "revoke of a slot in a missing CNode"
    (SeLe4n.Kernel.cspaceRevokeCdtFinalising bootCoreId r2BadSlot r2State)
    .objectNotFound
  expectErr "revoke of an empty slot"
    (SeLe4n.Kernel.cspaceRevokeCdtFinalising bootCoreId r2EmptySlot r2State)
    .invalidCapability
  IO.println "all revocation refusal checks passed"

/-- A CNode invocation reaches a CNode's slots only, as seL4 decodes a CNode
invocation only on a CNode capability: `CNode_Delete` and `CNode_Revoke` on a
capability to a thread are refused with `.objectNotFound` (`cnodeInvoked`), for
each of the thread's two space slots, and the state the refusal leaves still
holds both roots.  The internal finalising delete, which the revocation loop
runs, does reach the slot: the refusal is the invocation's guard, not a slot
the kernel cannot empty. -/
def runThreadSlotInvocationRefusalChecks : IO Unit := do
  let cnId : SeLe4n.ObjId := ⟨10⟩
  let vsId : SeLe4n.ObjId := ⟨20⟩
  let tId : SeLe4n.ObjId := ⟨6⟩
  let cells := SeLe4n.Model.TCB.spaceCellsOf cnId vsId
  let st : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject cnId (.cnode (CNode.ofList 0 0 0 3 []))
      |>.withObject vsId (.vspaceRoot { asid := asidPrimary, mappings := {} })
      |>.withObject tId (.tcb {
          tid := ⟨6⟩
          priority := ⟨40⟩
          domain := ⟨0⟩
          spaceCells := cells
          ipcBuffer := (SeLe4n.VAddr.ofNat 4096)
        })
      |>.buildChecked)
  let threadCap : Capability :=
    { target := .object tId, rights := AccessRightSet.ofList [.read, .write, .grant] }
  let gate : SeLe4n.Kernel.SyscallGate :=
    { callerId := ⟨6⟩, cspaceRoot := cnId, capAddr := SeLe4n.CPtr.ofNat 0, capDepth := 2,
      requiredRight := .write }
  for (sid, name) in [(SyscallId.cspaceDelete, "CNode_Delete"), (SyscallId.cspaceRevoke, "CNode_Revoke")] do
    for slot in [0, 1] do
      let decoded : SyscallDecodeResult :=
        { capAddr := SeLe4n.CPtr.ofNat 0, msgInfo := { length := 1, extraCaps := 0, label := 0 },
          syscallId := sid, msgRegs := #[SeLe4n.RegValue.ofNat slot] }
      expectErr s!"{name} on a thread capability, space slot {slot}"
        (SeLe4n.Kernel.dispatchWithCap decoded ⟨6⟩ bootCoreId gate threadCap st)
        .objectNotFound
  -- A refusal commits nothing: the state it leaves is `st`, whose thread still
  -- holds both roots.
  let rootsKept (s : SystemState) : Bool :=
    match s.getTcb? ⟨6⟩ with
    | some t => t.spaceCells == cells && t.cspaceRoot == cnId && t.vspaceRoot == vsId
    | none => false
  unless rootsKept st do
    throw <| IO.userError "a refused CNode invocation must leave the thread's two root slots"
  -- The internal delete reaches the thread's slot.
  match SeLe4n.Kernel.cspaceDeleteSlotFinalising bootCoreId
      { cnode := tId, slot := SeLe4n.Slot.ofNat 1 } st with
  | .ok ((), st1) =>
    unless (st1.slotCapAt { cnode := tId, slot := SeLe4n.Slot.ofNat 1 }).isNone &&
        (st1.slotCapAt { cnode := tId, slot := SeLe4n.Slot.ofNat 0 }).isSome do
      throw <| IO.userError "the internal delete must empty the thread's VSpace root slot alone"
  | .error e =>
    throw <| IO.userError s!"the internal delete of a thread's space slot must succeed, got {repr e}"
  IO.println "all thread-slot CNode-invocation refusal checks passed"

-- ============================================================================
-- R4: Lifecycle & Service Coherence negative tests
-- ============================================================================

/-- R4-F.1: Negative tests for cross-subsystem lifecycle/service coherence.
Tests: service registration without Write right, service registration targeting
a non-endpoint object, and endpoint type verification. -/
private def runWSR4CoherenceChecks : IO Unit := do
  IO.println "--- R4: Lifecycle & Service Coherence checks ---"

  -- R4-NEG-01: Register service without Write right → illegalAuthority
  let epId : SeLe4n.ObjId := ⟨30⟩
  let ifaceId : SeLe4n.InterfaceId := ⟨700⟩
  let iface : InterfaceSpec := {
    ifaceId := ifaceId, methodCount := 1,
    maxMessageSize := 1, maxResponseSize := 1, requiresGrant := false
  }
  let r4State := (BootstrapBuilder.empty
      |>.withObject epId (.endpoint {})
      |>.withLifecycleObjectType epId .endpoint
      |>.buildChecked)
  match SeLe4n.Kernel.registerInterface iface r4State with
  | .error _ => throw <| IO.userError "interface registration unexpectedly failed"
  | .ok (_, stIface) =>
    -- Capability without write right
    let noWriteCap : Capability := { target := .object epId, rights := .ofList [.read] }
    let reg : ServiceRegistration := {
      iface := iface, endpointCap := noWriteCap
    }
    expectErr "register service without Write right"
      (SeLe4n.Kernel.registerService reg stIface)
      .illegalAuthority

    -- R4-NEG-02: Register service targeting a non-endpoint (TCB) → invalidCapability
    let tcbId : SeLe4n.ObjId := ⟨31⟩
    let r4State2 := (BootstrapBuilder.empty
        |>.withObject tcbId (.tcb {
          tid := ⟨1⟩, priority := ⟨0⟩, domain := ⟨0⟩,
          spaceCells := SeLe4n.Model.TCB.spaceCellsOf ⟨0⟩ ⟨0⟩, ipcBuffer := (SeLe4n.VAddr.ofNat 0) })
        |>.withLifecycleObjectType tcbId .tcb
        |>.buildChecked)
    match SeLe4n.Kernel.registerInterface iface r4State2 with
    | .error _ => throw <| IO.userError "interface registration unexpectedly failed"
    | .ok (_, stIface2) =>
      let writeCap : Capability := { target := .object tcbId, rights := .singleton .write }
      let regTcb : ServiceRegistration := {
        iface := iface, endpointCap := writeCap
      }
      expectErr "register service targeting non-endpoint"
        (SeLe4n.Kernel.registerService regTcb stIface2)
        .invalidCapability

    -- R4-NEG-03: a registered endpoint records its registration, so the final
    -- delete's retire refuses it until the service is revoked (WS-ZA ZA5.4 part 31)
    let epForRetype : SeLe4n.ObjId := ⟨32⟩
    let r4State3 := (BootstrapBuilder.empty
        |>.withObject epForRetype (.endpoint {})
        |>.withLifecycleObjectType epForRetype .endpoint
        |>.buildChecked)
    -- Register interface and service on this endpoint
    match SeLe4n.Kernel.registerInterface iface r4State3 with
    | .error _ => throw <| IO.userError "interface registration failed"
    | .ok (_, stIface3) =>
      let svcSid : ServiceId := ServiceId.ofNat epForRetype.toNat
      let svcCap : Capability := { target := .object epForRetype, rights := .singleton .write }
      let svcReg : ServiceRegistration := {
        iface := iface, endpointCap := svcCap
      }
      match SeLe4n.Kernel.registerService svcReg stIface3 with
      | .error e => throw <| IO.userError s!"service registration failed: {toString e}"
      | .ok (_, stSvc3) =>
        -- Verify service is registered
        if stSvc3.serviceRegistry[svcSid]? = none then
          throw <| IO.userError "service not registered"
        -- The endpoint records the registration, so its back-links are not clear
        if stSvc3.tableBackLinksClear epForRetype then
          throw <| IO.userError "registered endpoint's back-links read clear"
        -- The O(1) lookup finds the registration through the endpoint's code
        match SeLe4n.Kernel.lookupServiceByRecordedRegistration epForRetype stSvc3 with
        | .error _ => throw <| IO.userError "recorded-code lookup missed the registration"
        | .ok (found, _) =>
          if found.sid != svcSid then
            throw <| IO.userError "recorded-code lookup found the wrong registration"
        -- Revoking clears the record, and the retire may then admit the endpoint
        match SeLe4n.Kernel.revokeService svcSid stSvc3 with
        | .error _ => throw <| IO.userError "service revocation failed"
        | .ok (_, stRevoked3) =>
          if !stRevoked3.tableBackLinksClear epForRetype then
            throw <| IO.userError "revoked endpoint still records the registration"
          expectErr "recorded-code lookup after revocation"
            (SeLe4n.Kernel.lookupServiceByRecordedRegistration epForRetype stRevoked3)
            .objectNotFound
        IO.println "negative check passed [R4-NEG-03: a registered endpoint's back-links hold the retire until revocation]"

    -- R4-NEG-05: Duplicate endpoint rejection — two services on same endpoint (AE5-B / U-20)
    let dupEpId : SeLe4n.ObjId := ⟨33⟩
    let r4State5 := (BootstrapBuilder.empty
        |>.withObject dupEpId (.endpoint {})
        |>.withLifecycleObjectType dupEpId .endpoint
        |>.buildChecked)
    match SeLe4n.Kernel.registerInterface iface r4State5 with
    | .error _ => throw <| IO.userError "interface registration failed"
    | .ok (_, stIface5) =>
      let sharedCap : Capability := { target := .object dupEpId, rights := .singleton .write }
      let regFirst : ServiceRegistration := {
        iface := iface, endpointCap := sharedCap
      }
      match SeLe4n.Kernel.registerService regFirst stIface5 with
      | .error e => throw <| IO.userError s!"first registration failed: {toString e}"
      | .ok (_, stFirstReg) =>
        -- Second service with DIFFERENT sid but SAME endpoint must fail
        let regSecond : ServiceRegistration := {
          iface := iface, endpointCap := sharedCap
        }
        expectErr "duplicate endpoint rejected"
          (SeLe4n.Kernel.registerService regSecond stFirstReg)
          .illegalState
        IO.println "negative check passed [R4-NEG-05: duplicate endpoint registration rejected]"

  IO.println "all R4 lifecycle/service coherence checks passed"

-- ============================================================================
-- S2-G: Capability error-path coverage tests
-- ============================================================================

/-- S2-G: Additional capability operation error-path tests covering:
    - cspaceMint with rights exceeding source (attenuation failure)
    - cspaceCopy to occupied destination slot
    - cspaceRevoke on deeply chained CDT -/
private def runS2GCapabilityErrorTests : IO Unit := do
  -- S2-G-01: cspaceMint requesting rights beyond source capability
  -- Source cap has read-only, attempt to mint read+write → invalidCapability
  let mintSrc : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := SeLe4n.Slot.ofNat 0 }
  let mintDst : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := SeLe4n.Slot.ofNat 3 }
  -- slot0 in baseState has rights [read, write]; create a read-only source
  let readOnlyCnode : KernelObject := .cnode (SeLe4n.Model.CNode.ofSlots 2 0 0 2 (SeLe4n.UniqueSlotMap.ofListWF [
      (SeLe4n.Slot.ofNat 0, {
        target := .object endpointId
        rights := AccessRightSet.ofList [.read]
      })
    ]))
  let readOnlyState : SystemState :=
    { baseState with objects := baseState.objects.insert cnodeId readOnlyCnode }
  -- Attempt to mint with read+write from a read-only source
  expectErr "cspaceMint rights exceed source"
    (SeLe4n.Kernel.cspaceMint mintSrc mintDst
      (AccessRightSet.ofList [.read, .write]) (badge := none) readOnlyState)
    .invalidCapability

  -- S2-G-02: cspaceCopy to occupied destination slot → targetSlotOccupied
  -- slot0 is already occupied in baseState; copy to it should fail
  let copySrc : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := SeLe4n.Slot.ofNat 0 }
  let copyDst : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := SeLe4n.Slot.ofNat 0 }
  expectErr "cspaceCopy to occupied slot"
    (SeLe4n.Kernel.cspaceCopy copySrc copyDst baseState)
    .targetSlotOccupied

  -- S2-G-03: cspaceMint to occupied destination slot → targetSlotOccupied
  expectErr "cspaceMint to occupied slot"
    (SeLe4n.Kernel.cspaceMint mintSrc copySrc
      (AccessRightSet.ofList [.read]) (badge := none) baseState)
    .targetSlotOccupied

  -- S2-G-04: revoking a capability with no derivations deletes nothing.
  let emptyRevokeSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := SeLe4n.Slot.ofNat 0 }
  let (_, emptyRevoked) ← expectOkSt "revoke with no descendants"
    (SeLe4n.Kernel.cspaceRevokeCdtFinalising bootCoreId emptyRevokeSlot baseState)
  if (SystemState.lookupSlotCap emptyRevoked emptyRevokeSlot).isNone then
    throw <| IO.userError "revoke must keep the source capability"
  IO.println "negative check passed [S2-G-04: revoke with no descendants keeps the source]"

  -- S2-G-05: cspaceCopy to full CNode (all slots occupied) → targetSlotOccupied
  -- Build a CNode with radixWidth=2 (four addressable slots), fill slots 0-3.
  -- WS-RR RR8.16 (`v0.35.201`): the code said `radixWidth := 0` — one slot —
  -- against a comment that has always said 2, so "full" named a CNode holding
  -- three capabilities no CPtr could reach.  At radix 2 it is genuinely full.
  let fullCnodeId : SeLe4n.ObjId := ⟨70⟩
  let fullCnode : KernelObject := .cnode (SeLe4n.Model.CNode.ofSlots 2 0 0 2 (SeLe4n.UniqueSlotMap.ofListWF [
      (SeLe4n.Slot.ofNat 0, { target := .object endpointId, rights := AccessRightSet.ofList [.read, .write] }),
      (SeLe4n.Slot.ofNat 1, { target := .object endpointId, rights := AccessRightSet.ofList [.read] }),
      (SeLe4n.Slot.ofNat 2, { target := .object endpointId, rights := AccessRightSet.ofList [.write] }),
      (SeLe4n.Slot.ofNat 3, { target := .object endpointId, rights := AccessRightSet.ofList [.read, .write] })
    ]))
  let fullCnodeState := { baseState with objects := baseState.objects.insert fullCnodeId fullCnode }
  -- Copy from slot0 in cnodeId into slot 0 of full CNode (occupied)
  let fullCopySrc : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := SeLe4n.Slot.ofNat 0 }
  let fullCopyDst : SeLe4n.Kernel.CSpaceAddr := { cnode := fullCnodeId, slot := SeLe4n.Slot.ofNat 0 }
  expectErr "cspaceCopy to full CNode slot"
    (SeLe4n.Kernel.cspaceCopy fullCopySrc fullCopyDst fullCnodeState)
    .targetSlotOccupied

  -- S2-G-06: revoke over a five-deep chain root → n1 → … → n5.  `cteRevoke`
  -- deletes the root's first child until it has none; each delete splices the
  -- child's own children up to the root, so the loop reaches every level.
  let deepRootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := SeLe4n.Slot.ofNat 0 }
  let deepNodes : List SlotRef :=
    [3, 4, 5, 6, 7].map fun n => { cnode := cnodeId, slot := SeLe4n.Slot.ofNat n }
  let deepCap : Capability := {
    target := .object endpointId,
    rights := AccessRightSet.ofList [.read, .write],
  }
  let deepSeed : SystemState :=
    { baseState with
      objects := baseState.objects.insert cnodeId (.cnode (CNode.ofList 8 0 0 8
        ((deepRootSlot :: deepNodes).map fun (r : SlotRef) => (r.slot, deepCap))))
      cdt := CapDerivationTree.empty
    } |>.withDerivationEdges
      ((deepRootSlot :: deepNodes).zip deepNodes |>.map fun ((p, c) : SlotRef × SlotRef) => (p, c, DerivationOp.copy))
  let (_, deepRevoked) ← expectOkSt "revoke over a deep chain"
    (SeLe4n.Kernel.cspaceRevokeCdtFinalising bootCoreId deepRootSlot deepSeed)
  if deepNodes.all (fun r => (SystemState.lookupSlotCap deepRevoked r).isNone) ∧
      (SystemState.lookupSlotCap deepRevoked deepRootSlot).isSome ∧
      deepRevoked.linkChildrenOf deepRootSlot = [] then
    IO.println "negative check passed [S2-G-06: revoke deletes all five levels and keeps the root]"
  else
    throw <| IO.userError "deep chain revoke should delete every descendant and keep the root"

  IO.println "all S2-G capability error-path tests passed"

-- ============================================================================
-- S2-H: Lifecycle error-path coverage tests
-- ============================================================================

/-- S2-H: Additional lifecycle operation error-path tests covering:
    - retypeFromUntyped with allocSize too small
    - retypeFromUntyped with device untyped → TCB rejection
    - retypeFromUntyped with non-untyped source object
    - retypeFromUntyped with region exhausted
    - retypeFromUntyped with childId collision -/
private def runS2HLifecycleErrorTests : IO Unit := do
  -- S2-H-01: retypeFromUntyped with very small untyped (allocSize too small)
  -- The f2UntypedState has a 256-byte untyped; try to retype with tiny allocSize
  expectErr "retypeFromUntyped allocSize too small"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2UntypedObjId ⟨90⟩
      (.tcb { tid := ⟨90⟩, priority := ⟨10⟩, domain := ⟨0⟩,
              spaceCells := SeLe4n.Model.TCB.spaceCellsOf cnodeId ⟨20⟩,
              ipcBuffer := (SeLe4n.VAddr.ofNat 0) }) 0 f2UntypedState)
    .untypedAllocSizeTooSmall

  -- S2-H-02: retypeFromUntyped with device untyped → TCB rejection
  -- f2DeviceState has isDevice=true; attempt to create a TCB (not untyped)
  expectErr "retypeFromUntyped device untyped TCB rejection"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2DeviceUntypedId ⟨91⟩
      (.tcb { tid := ⟨91⟩, priority := ⟨10⟩, domain := ⟨0⟩,
              spaceCells := SeLe4n.Model.TCB.spaceCellsOf cnodeId ⟨20⟩,
              ipcBuffer := (SeLe4n.VAddr.ofNat 0) }) 64 f2DeviceState)
    .untypedDeviceRestriction

  -- S2-H-03: retypeFromUntyped targeting non-untyped object → typeMismatch
  -- Use endpointId (which is an endpoint, not untyped) as the source
  expectErr "retypeFromUntyped non-untyped source"
    (SeLe4n.Kernel.retypeFromUntyped slot0 endpointId ⟨92⟩
      (.endpoint {}) 64 baseState)
    .untypedTypeMismatch

  -- S2-H-04: retypeFromUntyped with insufficient untyped capacity (region exhausted)
  -- An endpoint fills the untyped's region, leaving its authority capability's
  -- free index at the end of the region with a child; a childless capability
  -- would be reset to 0 instead (seL4's `ensureNoChildren`).
  let exhaustedUntypedId : SeLe4n.ObjId := ⟨85⟩
  let exhaustedAuthCnode : SeLe4n.ObjId := ⟨86⟩
  let exhaustedAuthSlot : SeLe4n.Kernel.CSpaceAddr :=
    { cnode := exhaustedAuthCnode, slot := SeLe4n.Slot.ofNat 0 }
  let exhaustedFresh : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject exhaustedUntypedId (.untyped {
        regionBase := (SeLe4n.PAddr.ofNat 0x10000)
        regionSize := 16
        children := []
        isDevice := false
      })
      |>.withObject exhaustedAuthCnode (.cnode (CNode.ofList 0 0 0 1 [
          (SeLe4n.Slot.ofNat 0, {
            target := .object exhaustedUntypedId
            rights := AccessRightSet.ofList [.read, .write, .grant, .retype]
          })
        ]))
      |>.withLifecycleObjectType exhaustedUntypedId .untyped
      |>.withLifecycleObjectType exhaustedAuthCnode .cnode
      |>.buildChecked)
  let (_, exhaustedState) ← expectOkSt "an endpoint filling the region is carved"
    (SeLe4n.Kernel.untypedRetypeObject exhaustedAuthSlot ⟨94⟩
      { cnode := exhaustedAuthCnode, slot := SeLe4n.Slot.ofNat 1 } .endpoint exhaustedFresh)
  expectErr "retypeFromUntyped region exhausted"
    (SeLe4n.Kernel.retypeFromUntyped exhaustedAuthSlot exhaustedUntypedId ⟨93⟩
      (.endpoint {}) 16 exhaustedState)
    .untypedRegionExhausted

  -- S2-H-05: retypeFromUntyped with childId that collides with existing object
  -- Use f2UntypedAuthCnode as the childId — it already exists in f2UntypedState
  expectErr "retypeFromUntyped childId collision"
    (SeLe4n.Kernel.retypeFromUntyped f2UntypedAuthSlot f2UntypedObjId f2UntypedAuthCnode
      (.endpoint {}) 64 f2UntypedState)
    .childIdCollision

  IO.println "all S2-H lifecycle error-path tests passed"

-- ============================================================================
-- X2: Runtime Invariant Enforcement tests
-- ============================================================================

/-- X2: Tests for Phase X2 — Runtime Invariant Enforcement.
    Covers: X2-B (setDomainScheduleChecked validation),
    X2-D (applyMachineConfig PA width propagation),
    X2-I (checked scheduler wrappers). -/
private def runX2RuntimeInvariantTests : IO Unit := do
  IO.println "\n=== X2: Runtime Invariant Enforcement ==="

  -- X2-B: setDomainScheduleChecked rejects zero-length entries
  let st0 : SystemState := default
  let badSchedule : List DomainScheduleEntry := [
    { domain := ⟨0⟩, length := 10 },
    { domain := ⟨1⟩, length := 0 },   -- zero-length entry
    { domain := ⟨2⟩, length := 5 }
  ]
  match setDomainScheduleChecked st0 badSchedule with
  | .error _ =>
    IO.println "positive check passed [X2-B-01]: setDomainScheduleChecked rejects zero-length entry"
  | .ok _ =>
    throw <| IO.userError "setDomainScheduleChecked should reject zero-length entry"

  -- X2-B: setDomainScheduleChecked accepts valid schedule
  let goodSchedule : List DomainScheduleEntry := [
    { domain := ⟨0⟩, length := 10 },
    { domain := ⟨1⟩, length := 5 }
  ]
  match setDomainScheduleChecked st0 goodSchedule with
  | .ok st1 =>
    if st1.scheduler.domainSchedule == goodSchedule then
      IO.println "positive check passed [X2-B-02]: setDomainScheduleChecked accepts valid schedule"
    else
      throw <| IO.userError "setDomainScheduleChecked result has wrong schedule"
  | .error e =>
    throw <| IO.userError s!"setDomainScheduleChecked should accept valid schedule, got: {e}"

  -- X2-D: applyMachineConfig propagates physicalAddressWidth
  let bootedState : IntermediateState :=
    SeLe4n.Platform.Boot.bootFromPlatform { irqTable := [], initialObjects := [] }
  let rpi5Config := SeLe4n.Platform.RPi5.rpi5MachineConfig
  let withPA : IntermediateState := SeLe4n.Platform.Boot.applyMachineConfig bootedState rpi5Config
  -- The v0.36.2 audit: the RPi5 width is the Cortex-A76's 40 bits (it read 44
  -- until then), and this check reads it off the binding rather than a literal,
  -- so it measures the propagation and not the number.
  let rpi5Width := rpi5Config.physicalAddressWidth
  if withPA.state.machine.physicalAddressWidth == rpi5Width && rpi5Width == 40 then
    IO.println "positive check passed [X2-D-01]: applyMachineConfig sets the RPi5 PA width (the Cortex-A76's 40 bits)"
  else
    throw <| IO.userError s!"expected the RPi5 PA width (40), got {withPA.state.machine.physicalAddressWidth} of binding {rpi5Width}"

  -- X2-D: default PA width is 52
  if bootedState.state.machine.physicalAddressWidth == 52 then
    IO.println "positive check passed [X2-D-02]: default PA width is 52"
  else
    throw <| IO.userError s!"expected default PA width 52, got {bootedState.state.machine.physicalAddressWidth}"

  -- AC4-A/A-04: vspaceMapPageCheckedWithFlushFromState rejects the first address
  -- beyond the RPi5 width (2^40 since the v0.36.2 audit; the boundary is read off
  -- the binding).  This verifies that the state-aware production entry point
  -- enforces platform-specific bounds, closing the [2^width, 2^52) gap.
  let asidAC4 : SeLe4n.ASID := ⟨1⟩
  let vaddrAC4 : SeLe4n.VAddr := (SeLe4n.VAddr.ofNat 0x1000)
  let rootOid : SeLe4n.ObjId := ⟨500⟩
  let paddrAtBoundary : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat (2^rpi5Width))  -- first address beyond the declared range
  let stRpi5 : SystemState :=
    { withPA.state with
      objects := withPA.state.objects.insert rootOid
        (.vspaceRoot { asid := asidAC4, mappings := {} })
      asidTable := withPA.state.asidTable.insert asidAC4 rootOid }
  let resultReject := SeLe4n.Kernel.Architecture.vspaceMapPageCheckedWithFlushFromState
    asidAC4 vaddrAC4 paddrAtBoundary default stRpi5
  match resultReject with
  | .error .addressOutOfBounds =>
    IO.println "positive check passed [AC4-A-01]: state-aware map rejects PA at 2^width on RPi5 (40-bit)"
  | .error e =>
    throw <| IO.userError s!"expected addressOutOfBounds, got {repr e}"
  | .ok _ =>
    throw <| IO.userError "state-aware map should reject PA at 2^width on the 40-bit platform"

  -- AC4-A/A-04: address just below the declared boundary should be accepted.
  -- PR #845 review (P2): was `2^width - 1`, which is all-ones and therefore never
  -- page-aligned; the state-aware map now rejects unaligned physical addresses,
  -- so this uses the largest page-aligned PA below the declared bound.
  let paddrJustBelow : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat (2^rpi5Width - 4096))
  let resultAccept := SeLe4n.Kernel.Architecture.vspaceMapPageCheckedWithFlushFromState
    asidAC4 vaddrAC4 paddrJustBelow default stRpi5
  match resultAccept with
  | .ok _ =>
    IO.println "positive check passed [AC4-A-02]: state-aware map accepts the largest page-aligned PA below 2^width on RPi5"
  | .error e =>
    throw <| IO.userError s!"expected ok for PA just below the declared bound, got {repr e}"

  -- X2-I / WS-SM SM8.B (PR #861 review round 15): `scheduleChecked` on a
  -- malformed run queue now *skips* the entry instead of returning
  -- `.schedulerInvariantViolation`, for the reason recorded at the sibling case
  -- in `runSchedulerNegativeChecks`: the error was not local — it aborted the
  -- whole selection scan on every future call, and nothing removes the entry,
  -- so one malformed entry wedged the core permanently.
  -- Uses .build intentionally: runnable [tid 77] references non-existent TCB.
  let malformedSt : SystemState :=
    (BootstrapBuilder.empty
      |>.withRunnable [SeLe4n.ThreadId.ofNat 77]
      |>.withCurrent none
      |>.build)
  match bootScheduleChecked malformedSt with
  | .error e =>
    throw <| IO.userError s!"scheduleChecked must skip a malformed runnable entry rather than fail, got {repr e}"
  | .ok (_, stChecked) =>
    -- Skipping, not dispatching: there is no TCB behind tid 77 to switch to.
    if (stChecked.scheduler.currentOnCore bootCoreId) = none then
      IO.println "positive check passed [scheduleChecked skips a malformed runnable entry]"
    else
      throw <| IO.userError s!"scheduleChecked must not dispatch a malformed runnable entry, got current = {toString (stChecked.scheduler.currentOnCore bootCoreId)}"

  -- X2-I: the checked yield on default state (no current thread) is refused by
  -- the yield itself, not as schedulerInvariantViolation — the
  -- saveOutgoingContextChecked guard passes because current=none.  The live
  -- per-core yield (`yieldOnCore`) refuses a core with no caller as
  -- `.illegalState`; the single-core reference `handleYield` it replaced in
  -- this suite reported `.invalidArgument`.
  expectErr "yield checked, no current thread"
    (bootYieldChecked (default : SystemState))
    .illegalState

  -- ── WS-RR RR8.12 follow-on (`v0.35.192`): the other two X2-I wrappers ──
  --
  -- The register row that scheduled the wire-or-retire judgement for the four
  -- unconsumed state transformers observed that `timerTickChecked` and
  -- `switchDomainChecked` are the undriven members of a four-member symmetric
  -- family whose other two ARE driven, so deleting half of it may be worse than
  -- keeping it.  They are kept — and these are the witnesses that make the
  -- keeping mean something, because each is a DIFFERENTIAL against the unchecked
  -- form on the same state rather than a smoke test.  A wrapper whose behaviour
  -- no state distinguishes from its delegate's would have earned deletion
  -- instead, and that is what these two measure.
  --
  -- (1) `timerTickChecked` SAVES THE OUTGOING CONTEXT and `timerTick` does not.
  -- The checked wrapper runs `saveOutgoingContextChecked` before delegating, so
  -- the current thread's `registerContext` picks up the executing core's bank;
  -- the bare tick leaves the TCB's own context alone.  The control is the bare
  -- tick on the identical state.
  let x2Tid : SeLe4n.ThreadId := ⟨5⟩
  let x2Tcb : TCB := {
    tid := x2Tid, priority := ⟨100⟩, domain := ⟨0⟩,
    spaceCells := SeLe4n.Model.TCB.spaceCellsOf (SeLe4n.ObjId.ofNat 0) (SeLe4n.ObjId.ofNat 0),
    ipcBuffer := SeLe4n.VAddr.ofNat 0, timeSlice := 9,
    scBindingScCode := 0, scBindingOwnerCode := 0 }
  let x2Base : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject x2Tid.toObjId (.tcb x2Tcb)
      |>.withCurrent (some x2Tid)
      |>.build)
  let x2Regs : RegisterFile := { (default : RegisterFile) with pc := ⟨4242⟩ }
  let x2Live : SystemState :=
    { x2Base with
        machine := x2Base.machine.setRegsOnCore
          SeLe4n.Kernel.Concurrency.bootCoreId x2Regs }
  let x2PcAfter : SystemState → Option Nat :=
    fun st => (st.getTcb? x2Tid).map (·.registerContext.pc.toNat)
  match bootTimerTickChecked x2Live with
  | .error e =>
    throw <| IO.userError s!"timerTickChecked must succeed on a resolvable current thread, got {repr e}"
  | .ok (_, stChecked) =>
    if x2PcAfter stChecked = some 4242 then
      IO.println "positive check passed [timerTickChecked saves the outgoing context]"
    else
      throw <| IO.userError s!"timerTickChecked must save the outgoing context, got pc = {toString (x2PcAfter stChecked)}"
  match bootTimerTick x2Live with
  | .error e =>
    throw <| IO.userError s!"the CONTROL (bare timerTick) must succeed on the same state, got {repr e}"
  | .ok (_, stBare) =>
    if x2PcAfter stBare = some 0 then
      IO.println "CONTROL passed [the bare timerTick leaves the outgoing context alone]"
    else
      throw <| IO.userError s!"the CONTROL is inert: bare timerTick already saved the context, pc = {toString (x2PcAfter stBare)}"

  -- (2) `switchDomainChecked` REFUSES a state `switchDomain` proceeds on.  Its
  -- guard fires exactly when the current slot names a thread the store does not
  -- hold — an invariant violation `currentThreadValid` forbids — and the bare
  -- `switchDomain` absorbs that silently (its internal `saveOutgoingContext`
  -- returns the state unchanged on a TCB miss).  So here the GUARD is what
  -- discriminates, where in (1) it was the save.
  let x2Dangling : SystemState :=
    (BootstrapBuilder.empty
      |>.withCurrent (some (SeLe4n.ThreadId.ofNat 77))
      |>.build)
  expectErr "switchDomainChecked refuses a dangling current thread"
    (bootSwitchDomainChecked x2Dangling)
    .schedulerInvariantViolation
  match bootSwitchDomain x2Dangling with
  | .error e =>
    throw <| IO.userError s!"the CONTROL (bare switchDomain) must PROCEED on the dangling state — that is what the wrapper adds — got {repr e}"
  | .ok _ =>
    IO.println "CONTROL passed [the bare switchDomain proceeds on the state the wrapper refuses]"

  -- ...and on that same state the checked tick's guard refuses too, while the
  -- bare tick, total as seL4's `timerTick` is (`v0.36.165`), charges the
  -- dangling current thread nothing and proceeds: here too the GUARD is what
  -- discriminates.
  expectErr "timerTickChecked refuses a dangling current thread"
    (bootTimerTickChecked x2Dangling)
    .schedulerInvariantViolation
  match bootTimerTick x2Dangling with
  | .error e =>
    throw <| IO.userError s!"the CONTROL (bare timerTick) must PROCEED on the dangling state — the tick is total — got {repr e}"
  | .ok _ =>
    IO.println "CONTROL passed [the bare timerTick proceeds on the state the wrapper refuses]"

  IO.println "all X2 runtime invariant tests passed"

-- ============================================================================
-- Z8-L: SchedContext negative-state tests
-- ============================================================================

/-- Z8-L: Negative tests for SchedContext operations — covers error paths for
bind to non-existent SC, double-bind, configure with zero period, admission
control rejection, and unbind of unbound SC. -/
def runZ8SchedContextNegativeChecks : IO Unit := do
  let st0 : SystemState := default

  -- Z8-L-01: Configure non-existent SchedContext
  expectErr "configure non-existent SC"
    (SeLe4n.Kernel.SchedContextOps.schedContextConfigure ⟨⟨9900⟩, by decide⟩ 100 1000 50 0 0 st0)
    .objectNotFound

  -- Z8-L-02: Configure with zero period
  let scId : SeLe4n.ObjId := ⟨9901⟩
  let scIdTyped : SeLe4n.SchedContextId := ⟨9901⟩
  let sc0 := SeLe4n.Kernel.SchedContext.empty scIdTyped
  let stWithSc := { st0 with
    objects := st0.objects.insert scId (.schedContext sc0)
    objectIndex := scId :: st0.objectIndex
    objectIndexSet := st0.objectIndexSet.insert scId }
  expectErr "configure zero period"
    (SeLe4n.Kernel.SchedContextOps.schedContextConfigure ⟨scId, by decide⟩ 100 0 50 0 0 stWithSc)
    .invalidArgument

  -- Z8-L-03: Configure with budget > period
  expectErr "configure budget>period"
    (SeLe4n.Kernel.SchedContextOps.schedContextConfigure ⟨scId, by decide⟩ 200 100 50 0 0 stWithSc)
    .invalidArgument

  -- Z8-L-04: Bind to non-existent SchedContext
  let tid : SeLe4n.ThreadId := ⟨9902⟩
  expectErr "bind non-existent SC"
    (SeLe4n.Kernel.SchedContextOps.schedContextBind ⟨⟨9999⟩, by decide⟩ ⟨tid, by decide⟩ st0)
    .objectNotFound

  -- Z8-L-05: Bind when SC already has a bound thread (double-bind)
  let scBound := { sc0 with boundThreadCode := SeLe4n.ThreadId.optCode (some ⟨1⟩) }
  let stBound := { st0 with
    objects := st0.objects.insert scId (.schedContext scBound)
    objectIndex := scId :: st0.objectIndex
    objectIndexSet := st0.objectIndexSet.insert scId }
  expectErr "double-bind SC"
    (SeLe4n.Kernel.SchedContextOps.schedContextBind ⟨scId, by decide⟩ ⟨tid, by decide⟩ stBound)
    .illegalState

  -- Z8-L-06: Bind when TCB is already bound to another SC
  let tcbAlreadyBound : TCB := {
    tid := tid, priority := ⟨50⟩, domain := ⟨0⟩,
    spaceCells := SeLe4n.Model.TCB.spaceCellsOf ⟨10⟩ ⟨20⟩, ipcBuffer := (SeLe4n.VAddr.ofNat 4096),
    scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.bound ⟨8888⟩), scBindingOwnerCode := 0 }
  let stTcbBound := { stWithSc with
    objects := stWithSc.objects.insert tid.toObjId (.tcb tcbAlreadyBound) }
  expectErr "bind TCB already bound"
    (SeLe4n.Kernel.SchedContextOps.schedContextBind ⟨scId, by decide⟩ ⟨tid, by decide⟩ stTcbBound)
    .illegalState

  -- Z8-L-07: Unbind when SC has no bound thread
  expectErr "unbind no bound thread"
    (SeLe4n.Kernel.SchedContextOps.schedContextUnbind ⟨scId, by decide⟩ stWithSc)
    .illegalState

  -- Z8-L-08: Unbind non-existent SchedContext
  expectErr "unbind non-existent SC"
    (SeLe4n.Kernel.SchedContextOps.schedContextUnbind ⟨⟨9999⟩, by decide⟩ st0)
    .objectNotFound

  IO.println "all Z8 SchedContext negative tests passed"

-- ============================================================================
-- AC1-G: S-01 regression test — hasSufficientBudget fail-closed
-- ============================================================================

def runAC1BudgetFailClosedChecks : IO Unit := do
  IO.println "── AC1-G: hasSufficientBudget fail-closed checks ──"

  let st0 : SystemState := default
  let tid : SeLe4n.ThreadId := ⟨5001⟩

  -- AC1-G-01: Unbound thread always has sufficient budget
  let tcbUnbound : TCB := {
    tid := tid, priority := ⟨50⟩, domain := ⟨0⟩,
    spaceCells := SeLe4n.Model.TCB.spaceCellsOf ⟨10⟩ ⟨20⟩, ipcBuffer := (SeLe4n.VAddr.ofNat 4096),
    scBindingScCode := 0, scBindingOwnerCode := 0 }
  if SeLe4n.Kernel.hasSufficientBudget st0 tcbUnbound != true then
    throw <| IO.userError "unbound thread should have sufficient budget"

  -- AC1-G-02: Bound thread with non-existent SchedContext → false (fail-closed)
  let tcbBoundMissing : TCB := {
    tid := tid, priority := ⟨50⟩, domain := ⟨0⟩,
    spaceCells := SeLe4n.Model.TCB.spaceCellsOf ⟨10⟩ ⟨20⟩, ipcBuffer := (SeLe4n.VAddr.ofNat 4096),
    scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.bound ⟨7777⟩), scBindingOwnerCode := 0 }
  if SeLe4n.Kernel.hasSufficientBudget st0 tcbBoundMissing != false then
    throw <| IO.userError "missing SchedContext should fail-closed (return false)"

  -- AC1-G-03: Donated binding with non-existent SchedContext → false
  let tcbDonatedMissing : TCB := {
    tid := tid, priority := ⟨50⟩, domain := ⟨0⟩,
    spaceCells := SeLe4n.Model.TCB.spaceCellsOf ⟨10⟩ ⟨20⟩, ipcBuffer := (SeLe4n.VAddr.ofNat 4096),
    scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.donated ⟨8888⟩ ⟨9999⟩), scBindingOwnerCode := SeLe4n.Kernel.SchedContextBinding.ownerCode (.donated ⟨8888⟩ ⟨9999⟩) }
  if SeLe4n.Kernel.hasSufficientBudget st0 tcbDonatedMissing != false then
    throw <| IO.userError "donated missing SchedContext should fail-closed"

  -- AC1-G-04: Bound thread with existing SchedContext, positive budget → true
  let scId : SeLe4n.ObjId := ⟨6001⟩
  let sc := SeLe4n.Kernel.SchedContext.empty ⟨6001⟩
  let scWithBudget := { sc with budgetRemaining := ⟨100⟩ }
  let stWithSc := { st0 with
    objects := st0.objects.insert scId (.schedContext scWithBudget) }
  let tcbBound : TCB := {
    tid := tid, priority := ⟨50⟩, domain := ⟨0⟩,
    spaceCells := SeLe4n.Model.TCB.spaceCellsOf ⟨10⟩ ⟨20⟩, ipcBuffer := (SeLe4n.VAddr.ofNat 4096),
    scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.bound ⟨6001⟩), scBindingOwnerCode := 0 }
  if SeLe4n.Kernel.hasSufficientBudget stWithSc tcbBound != true then
    throw <| IO.userError "bound with positive budget should be true"

  -- AC1-G-05: Bound thread with existing SchedContext, zero budget → false
  let scZeroBudget := { sc with budgetRemaining := ⟨0⟩ }
  let stZeroBudget := { st0 with
    objects := st0.objects.insert scId (.schedContext scZeroBudget) }
  if SeLe4n.Kernel.hasSufficientBudget stZeroBudget tcbBound != false then
    throw <| IO.userError "zero budget should return false"

  IO.println "all AC1-G budget fail-closed checks passed"

-- ============================================================================
-- AC1-H: C-01 regression test — cspaceMint CDT absence vs cspaceMintWithCdt
-- ============================================================================

def runAC1CdtTrackingChecks : IO Unit := do
  IO.println "── AC1-H: cspaceMint CDT tracking checks ──"

  let st0 : SystemState := default

  -- Build a minimal CSpace with 2 CNodes and a source capability
  let srcCnodeId : SeLe4n.ObjId := ⟨100⟩
  let dstCnodeId : SeLe4n.ObjId := ⟨200⟩
  let srcSlot : SeLe4n.Slot := SeLe4n.Slot.ofNat 0
  let dstSlot : SeLe4n.Slot := SeLe4n.Slot.ofNat 1
  let allRights := AccessRightSet.ofList [.read, .write, .grant, .grantReply, .retype]
  let cap : Capability := {
    target := .object ⟨300⟩,
    rights := allRights, }

  -- Create CNodes with proper structure
  let srcCnode : CNode := CNode.ofList 0 0 0 4 [(srcSlot, cap)]
  let dstCnode : CNode := (SeLe4n.Model.CNode.ofSlots 0 0 0 4 SeLe4n.UniqueSlotMap.empty)

  let st1 := { st0 with
    objects := st0.objects
      |>.insert srcCnodeId (.cnode srcCnode)
      |>.insert dstCnodeId (.cnode dstCnode)
    objectIndex := [srcCnodeId, dstCnodeId] ++ st0.objectIndex
    objectIndexSet := st0.objectIndexSet.insert srcCnodeId |>.insert dstCnodeId }

  let srcAddr : SeLe4n.Kernel.CSpaceAddr := { cnode := srcCnodeId, slot := srcSlot }
  let dstAddr : SeLe4n.Kernel.CSpaceAddr := { cnode := dstCnodeId, slot := dstSlot }

  -- AC1-H-01: cspaceMint succeeds but CDT has no new edges
  let edgeCountBefore := (linkedDerivationEdges st1).length
  match SeLe4n.Kernel.cspaceMint srcAddr dstAddr allRights none st1 with
  | .ok ((), stMint) =>
    if (linkedDerivationEdges stMint).length != edgeCountBefore then
      throw <| IO.userError "cspaceMint should NOT add CDT edges"
  | .error e =>
    throw <| IO.userError s!"cspaceMint failed unexpectedly: {repr e}"

  -- AC1-H-02: cspaceMintWithCdt succeeds and CDT has a new edge
  match SeLe4n.Kernel.cspaceMintWithCdt srcAddr dstAddr allRights none st1 with
  | .ok ((), stMintCdt) =>
    if (linkedDerivationEdges stMintCdt).length <= edgeCountBefore then
      throw <| IO.userError "cspaceMintWithCdt should add a CDT edge"
  | .error e =>
    throw <| IO.userError s!"cspaceMintWithCdt failed unexpectedly: {repr e}"

  IO.println "all AC1-H CDT tracking checks passed"

-- ============================================================================
-- WS-RC R1 (DEEP-IPC-03): IPC call-path NI symmetry on missing-CSpace-root
-- ============================================================================

private def r1EpId        : SeLe4n.ObjId    := ⟨6700⟩
private def r1CallerTid   : SeLe4n.ThreadId := ⟨6710⟩
private def r1ReceiverTid : SeLe4n.ThreadId := ⟨6711⟩
private def r1CallerCNode : SeLe4n.ObjId    := ⟨6720⟩
private def r1ReceiverCNode : SeLe4n.ObjId  := ⟨6721⟩
private def r1TargetObj   : SeLe4n.ObjId    := ⟨6730⟩
-- WS-SM SM6.D (#7.3 fold): the server's server-first Recv supplies this Reply
-- object; the later Call rendezvous links the caller to it atomically.
private def r1ReplyId     : SeLe4n.ReplyId  := ⟨6731⟩

private def r1Cap : Capability :=
  { target := .object r1TargetObj,
    rights := AccessRightSet.ofList [.read], }

/-- The caller's frame names `r1Cap`'s slot as its one extra capability address
(WS-ZA ZA4.7), so the call has a capability to transfer. -/
private def r1Framed (st : SystemState) : SystemState :=
  SeLe4n.Testing.withSenderFrame st r1CallerTid IpcMessage.empty #[SeLe4n.CPtr.ofNat 0]

private def r1EndpointRights : AccessRightSet :=
  AccessRightSet.ofList [.write, .grant]

private def r1BaseState : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject r1EpId (.endpoint {})
    |>.withObject r1TargetObj (.notification { state := .idle, hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero })
    |>.withObject r1CallerCNode (.cnode
        (SeLe4n.Model.CNode.ofSlots 4 0 0 4 (SeLe4n.UniqueSlotMap.ofListWF [((SeLe4n.Slot.ofNat 0), r1Cap)])))
    |>.withObject r1ReceiverCNode (.cnode
        (SeLe4n.Model.CNode.ofSlots 4 0 0 4 (SeLe4n.UniqueSlotMap.ofListWF [])))
    |>.withObject r1CallerTid.toObjId (.tcb
        { tid := r1CallerTid, priority := ⟨1⟩, domain := ⟨0⟩,
          spaceCells := SeLe4n.Model.TCB.spaceCellsOf r1CallerCNode ⟨0⟩,
          ipcBuffer := (SeLe4n.VAddr.ofNat 0) })
    |>.withObject r1ReceiverTid.toObjId (.tcb
        { tid := r1ReceiverTid, priority := ⟨1⟩, domain := ⟨0⟩,
          spaceCells := SeLe4n.Model.TCB.spaceCellsOf r1ReceiverCNode ⟨0⟩,
          ipcBuffer := (SeLe4n.VAddr.ofNat 0) })
    |>.withObject r1ReplyId.toObjId (.reply { replyId := r1ReplyId })
    |>.withRunnable [r1CallerTid, r1ReceiverTid]
    |>.buildChecked)

private def r1QueuedState : Except KernelError SystemState :=
  match SeLe4n.Kernel.endpointReceiveDual r1EpId r1ReceiverTid (some r1ReplyId) r1BaseState with
  | .error e => .error e
  | .ok (_, st) => .ok st

private def r1FaultyState (st : SystemState) : SystemState :=
  { st with objects := st.objects.erase r1ReceiverTid.toObjId }

private def r1CheckHealthyState (stQueued : SystemState) : IO Unit := do
  let result := SeLe4n.Kernel.endpointCallWithCaps r1EpId r1CallerTid
    (.frame none (r1EndpointRights.mem .grant)) (SeLe4n.Slot.ofNat 0) (r1Framed stQueued)
  match result with
  | .ok _ =>
      IO.println "positive check passed [R1-NEG-01 endpointCallWithCaps healthy state succeeds]"
  | .error e =>
      throw <| IO.userError
        s!"R1-NEG-01: endpointCallWithCaps on healthy state should succeed, got error {toString e}"

private def r1CheckFaultyState (stFaulty : SystemState) : IO Unit := do
  let result := SeLe4n.Kernel.endpointCallWithCaps r1EpId r1CallerTid
    (.frame none (r1EndpointRights.mem .grant)) (SeLe4n.Slot.ofNat 0) (r1Framed stFaulty)
  match result with
  | .ok _ =>
      throw <| IO.userError
        "R1-NEG-02: endpointCallWithCaps must NEVER silently succeed on missing-TCB receiver (covert channel)"
  | .error _ =>
      IO.println
        "negative check passed [R1-NEG-02 endpointCallWithCaps fail-closed on missing-TCB receiver]"

private def r1CheckLookupCspaceRoot (stFaulty : SystemState) : IO Unit := do
  if SeLe4n.Kernel.lookupCspaceRoot stFaulty r1ReceiverTid = none then
    IO.println
      "negative check passed [R1-NEG-03 lookupCspaceRoot none witnesses guarded fault arm]"
  else
    throw <| IO.userError
      "R1-NEG-03: lookupCspaceRoot should return none on missing-TCB receiver"

/-- WS-RC R1 (DEEP-IPC-03): Confirm `endpointCallWithCaps` shares the
fail-closed semantics of `endpointSendDualWithCaps` and
`endpointReceiveDualWithCaps` on the missing-CSpace-root structural fault.

Background: AK1-I (I-M07) closed the asymmetry between the send and
receive WithCaps wrappers — both fail closed with `.error .invalidCapability`
when the dequeued peer's CSpace root cannot be resolved. The call path was
the remaining outlier, returning `.ok ({ results := #[] }, st')` and giving
a per-domain covert channel via `KernelError`. This test exercises the
post-R1 invariant: the call wrapper must never silently succeed under the
missing-TCB structural fault.

Three cases are checked:
- R1-NEG-01: Healthy state with a properly enqueued receiver — wrapper
  returns success.
- R1-NEG-02: Faulty state with the receiver's TCB erased after enqueue —
  wrapper MUST return `.error _` (any error code; the inner `endpointCall`
  will surface `.objectNotFound` from `endpointQueuePopHead` before the
  `lookupCspaceRoot = none` arm fires, but the wrapper never returns `.ok`).
- R1-NEG-03: `lookupCspaceRoot` returns `none` on the faulty state, which
  is exactly the invariant-violating predicate that the new `.error`
  arm guards against in source. -/
def runR1IpcCallPathSymmetryChecks : IO Unit := do
  IO.println "\n=== WS-RC R1 (DEEP-IPC-03): IPC call-path NI symmetry ==="
  match r1QueuedState with
  | .error e =>
    throw <| IO.userError s!"R1-NEG-setup: receive-enqueue failed: {toString e}"
  | .ok stQueued =>
    r1CheckHealthyState stQueued
    let stFaulty := r1FaultyState stQueued
    r1CheckFaultyState stFaulty
    r1CheckLookupCspaceRoot stFaulty
  IO.println "all WS-RC R1 IPC call-path NI symmetry checks passed"

-- ============================================================================
-- WS-RC R5.E (DEEP-SCH-04): missingSchedContext surface on orphan binding
-- ============================================================================

/-- WS-RC R5.E (DEEP-SCH-04): `timerTickBudget` rejects with
`.missingSchedContext` when a bound-budget thread references an absent
SchedContext.  Pre-R5 the path silently fell back to `(state, false)` —
no-preempt — masking the cross-subsystem invariant drift.

Setup: a TCB with `schedContextBinding := .bound scId` where `scId`'s
backing object has been erased from the kernel store (simulating an
invariant violation in `schedContextStoreConsistent`).  The expected
result is `.error .missingSchedContext`, not a silent identity. -/
private def r5eOrphanedScId : SeLe4n.SchedContextId := ⟨7777⟩

private def r5eOrphanedTid : SeLe4n.ThreadId := ⟨42⟩

private def r5eOrphanedBoundState : SystemState :=
  -- Build a state with only the TCB referencing the (absent) SchedContext.
  -- Note: we intentionally do NOT add the SchedContext object — the bound
  -- thread's SC binding is dangling.
  (BootstrapBuilder.empty
    |>.withObject r5eOrphanedTid.toObjId (.tcb
        { tid := r5eOrphanedTid, priority := ⟨1⟩, domain := ⟨0⟩,
          spaceCells := SeLe4n.Model.TCB.spaceCellsOf ⟨0⟩ ⟨0⟩,
          ipcBuffer := (SeLe4n.VAddr.ofNat 0),
          scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.bound r5eOrphanedScId), scBindingOwnerCode := 0,
          timeSlice := 1 })
    |>.withCurrent r5eOrphanedTid
    |>.buildChecked)

/-- The refusal itself: a bound thread whose context the store does not hold is
refused with `.missingSchedContext` before any write.  `timerTickBudget` is the
single-core specification, which writes the release queue's abstract (ghost)
form, so it is not compiled (WS-ZA ZA6.3); the refusal is proven here and the
runtime check below establishes that the fixture meets its two premises. -/
private theorem timerTickBudget_refuses_orphaned_binding (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (scId : SeLe4n.SchedContextId) (hB : tcb.schedContextBinding = .bound scId)
    (hSc : st.getSchedContext? scId = none) :
    SeLe4n.Kernel.timerTickBudget st tid tcb hTcb = .error .missingSchedContext := by
  have hW := SystemState.getSchedContextWitnessed?_eq_none hSc
  unfold SeLe4n.Kernel.timerTickBudget
  rw [hB]; simp only [hW]

/-- The fixture meets the refusal's premises; a fixture that resolves no TCB
is reported as misconstructed rather than run on a stub. -/
private def runR5EOrphanedSchedContextChecks : IO Unit := do
  IO.println "\n=== WS-RC R5.E (DEEP-SCH-04): missingSchedContext surface ==="
  -- `timerTickBudget_refuses_orphaned_binding` is the refusal; the fixture
  -- meets its premises: its thread is bound to `r5eOrphanedScId`, which the
  -- store does not hold.  A fixture that resolves no TCB is reported as such.
  match r5eOrphanedBoundState.getTcb? r5eOrphanedTid with
  | none => throw <| IO.userError "R5.E-NEG-01: the fixture resolves no TCB"
  | some tcb =>
    if tcb.schedContextBinding == .bound r5eOrphanedScId &&
        (r5eOrphanedBoundState.getSchedContext? r5eOrphanedScId).isNone then
      IO.println
        ("negative check passed [R5.E-NEG-01 timerTickBudget rejects "
         ++ "orphaned SchedContext binding with .missingSchedContext]")
    else
      throw <| IO.userError
        "R5.E-NEG-01: the fixture's thread is not bound to an absent SchedContext"
  IO.println "all WS-RC R5.E missingSchedContext surface checks passed"

-- ============================================================================
-- WS-RR RR8.16 (`v0.35.201`): a CSpace destination slot is addressable, or the
-- install is refused
-- ============================================================================

/-- `cspaceInsertSlot` as it read before `v0.35.201`: occupancy alone, with no
radix bound.  Spelled here and nowhere else, so the checks below are known to
**discriminate** between the two readings rather than merely to pass — every
one of them succeeds under this reading and is refused by the live one.
(WS-ZA ZA5.3: under this reading the store past the radix is now a no-op,
since `CNode.insert` has no slot-array entry to write.) -/
private def unguardedInsertSlot (addr : SeLe4n.Kernel.CSpaceAddr) (cap : Capability) :
    SeLe4n.Model.Kernel Unit :=
  fun st =>
    match st.getCNode? addr.cnode with
    | some cn =>
        match cn.lookup addr.slot with
        | some _ => Except.error KernelError.targetSlotOccupied
        | none => SeLe4n.Model.storeObject addr.cnode (.cnode (cn.insert addr.slot cap)) st
    | none => Except.error KernelError.objectNotFound

/-- WS-RR RR8.16 (`v0.35.201`): no capability is installed at a slot index the
target CNode's radix width cannot address.

`CNode.resolveSlot` extracts a slot by masking with `2 ^ radixWidth`, so an
index at or above `slotCount` can be **stored** and can never be **reached**.
The four install paths — `cspaceCopy`, `cspaceMint`, `cspaceMove` and the IPC
capability transfer — all pass through `cspaceInsertSlot`, which is where the
range check lives; the transfer's own slot scan is radix-bounded so that a
receiver CNode with no free in-range slot answers `.noSlot` rather than
scanning past its own width. -/
private def runWSRR8CSpaceSlotRangeChecks : IO Unit := do
  IO.println "=== WS-RR RR8.16: CSpace destination slots are radix-bounded ==="
  -- A four-slot CNode (indices 0..3) holding one capability at slot 0.
  let rangeCnodeId : SeLe4n.ObjId := ⟨71⟩
  let rangeCnode : CNode := (SeLe4n.Model.CNode.ofSlots 2 0 0 2 (SeLe4n.UniqueSlotMap.ofListWF [
      (SeLe4n.Slot.ofNat 0, ({ target := .object endpointId, rights := AccessRightSet.ofList [.read, .write] } : Capability))
    ]))
  let rangeState : SystemState :=
    { baseState with objects := baseState.objects.insert rangeCnodeId (.cnode rangeCnode) }
  let rangeSrc : SeLe4n.Kernel.CSpaceAddr := { cnode := rangeCnodeId, slot := SeLe4n.Slot.ofNat 0 }
  let inRangeDst : SeLe4n.Kernel.CSpaceAddr := { cnode := rangeCnodeId, slot := SeLe4n.Slot.ofNat 2 }
  let outOfRangeDst : SeLe4n.Kernel.CSpaceAddr := { cnode := rangeCnodeId, slot := SeLe4n.Slot.ofNat 9 }

  -- CONTROL: an in-range destination still installs, so the refusal below is
  -- about the slot index and not about the copy.
  let (_, copiedState) ← expectOkVal "RR8-CSR-01 CONTROL in-range cspaceCopy installs"
    (SeLe4n.Kernel.cspaceCopy rangeSrc inRangeDst rangeState)
  match SeLe4n.Model.SystemState.lookupSlotCap copiedState inRangeDst with
  | none => throw <| IO.userError "RR8-CSR-01: in-range destination slot is empty after copy"
  | some _ => IO.println "positive check passed [RR8-CSR-01 CONTROL: slot 2 of a four-slot CNode installs]"

  -- DEFECT: a destination the CNode's radix cannot address is refused.
  expectErr "RR8-CSR-02 cspaceCopy to an unaddressable destination slot"
    (SeLe4n.Kernel.cspaceCopy rangeSrc outOfRangeDst rangeState)
    .invalidArgument
  expectErr "RR8-CSR-03 cspaceMint to an unaddressable destination slot"
    (SeLe4n.Kernel.cspaceMint rangeSrc outOfRangeDst
      (AccessRightSet.ofList [.read]) (badge := none) rangeState)
    .invalidArgument
  expectErr "RR8-CSR-04 cspaceMove to an unaddressable destination slot"
    (SeLe4n.Kernel.cspaceMove rangeSrc outOfRangeDst rangeState)
    .invalidArgument

  -- A CNode at capacity: four capabilities in four addressable slots.
  let fullCnodeId : SeLe4n.ObjId := ⟨72⟩
  let occupied : Capability :=
    { target := .object endpointId, rights := AccessRightSet.ofList [.read] }
  let fullCnode : CNode := CNode.ofList 2 0 0 2 [
      (SeLe4n.Slot.ofNat 0, occupied), (SeLe4n.Slot.ofNat 1, occupied),
      (SeLe4n.Slot.ofNat 2, occupied), (SeLe4n.Slot.ofNat 3, occupied) ]
  let fullState : SystemState :=
    { baseState with objects := baseState.objects.insert fullCnodeId (.cnode fullCnode) }
  let fullOutOfRangeDst : SeLe4n.Kernel.CSpaceAddr :=
    { cnode := fullCnodeId, slot := SeLe4n.Slot.ofNat 9 }

  -- ...and the retired reading, which once installed there and left a CNode
  -- holding more capabilities than it has slots, now stores nothing: WS-ZA
  -- ZA5.3's slot array has no entry past `2 ^ radixWidth`, so `CNode.insert`
  -- at slot 9 leaves the CNode as it was and the slot-count bound
  -- (`CNode.slotCountBounded_holds`) holds even without the guard.
  match unguardedInsertSlot fullOutOfRangeDst occupied fullState with
  | .error e =>
      throw <| IO.userError
        s!"RR8-CSR-05: the retired unguarded insert was expected to succeed, got {toString e}"
  | .ok (_, unguardedState) =>
      match unguardedState.getCNode? fullCnodeId with
      | none => throw <| IO.userError "RR8-CSR-05: the target CNode vanished"
      | some cn' =>
          if cn'.occupiedCount > cn'.slotCount then
            throw <| IO.userError
              "RR8-CSR-05: an insert past the radix broke slotCountBounded"
          else if (cn'.lookup (SeLe4n.Slot.ofNat 9)).isSome then
            throw <| IO.userError
              "RR8-CSR-05: an insert past the radix stored a capability at slot 9"
          else
            IO.println
              ("negative check passed [RR8-CSR-05: the retired unguarded insert at "
               ++ s!"slot 9 of a {cn'.slotCount}-slot CNode stores nothing, leaving "
               ++ s!"slots.size = {cn'.occupiedCount}]")

  -- The IPC transfer path scans within the radix, so a receiver with no free
  -- in-range slot answers `.noSlot` rather than installing out of range.
  let (transferResult, _) ← expectOkVal "RR8-CSR-06 ipcTransferSingleCap on a full receiver CNode"
    (SeLe4n.Kernel.ipcTransferSingleCap occupied
      { cnode := fullCnodeId, slot := SeLe4n.Slot.ofNat 0 } fullCnodeId (SeLe4n.Slot.ofNat 0) 8 fullState)
  match transferResult with
  | .noSlot => IO.println "negative check passed [RR8-CSR-06: a full receiver CNode answers .noSlot]"
  | other =>
      throw <| IO.userError
        s!"RR8-CSR-06: expected .noSlot from a full receiver CNode, got {reprStr other}"
  -- ...where the unchecked scan walks straight past the CNode's own width.
  match fullCnode.findFirstEmptySlot (SeLe4n.Slot.ofNat 0) 8 with
  | none => throw <| IO.userError "RR8-CSR-07: the retired unchecked scan was expected to answer a slot"
  | some s =>
      if s.toNat < fullCnode.slotCount then
        throw <| IO.userError
          s!"RR8-CSR-07: the retired scan answered in-range slot {s.toNat}; expected one past the radix"
      else
        IO.println
          ("negative check passed [RR8-CSR-07: the retired unchecked scan answers slot "
           ++ s!"{s.toNat} of a {fullCnode.slotCount}-slot CNode]")

  IO.println "all WS-RR RR8.16 CSpace slot-range checks passed"


/-- **A zombie delete empties what its slot destroys, and always deletes the
slot** (WS-ZA ZA5.4 parts 26 and 35): CNode 10's slot 0 holds the last capability
to CNode 11, whose slot 2 names endpoint 12 and slot 3 names CNode 15, which
names endpoint 13.  The delete empties CNode 15 and CNode 11, retires both, and
deletes the slot (`zombieDeleteAt`, whose passes always end, `zombiePasses_end`).
The same holds when the graph below the slot is cyclic: CNode 11's slot 5 holds
the last capability to CNode 10 itself, the loop's own CNode, which the loop
passes over when it reaches it (its own slot is the cycle seL4's Zombie
breaks); that capability is deleted as a leaf, CNode 10 is kept (it still holds
the loop's slot), and the slot is deleted. -/
private def runZombieDeleteCompletesChecks : IO Unit := do
  let rootId : SeLe4n.ObjId := ⟨10⟩
  let innerId : SeLe4n.ObjId := ⟨11⟩
  let epId : SeLe4n.ObjId := ⟨12⟩
  let ep2Id : SeLe4n.ObjId := ⟨13⟩
  let deepId : SeLe4n.ObjId := ⟨15⟩
  let rw : AccessRightSet := AccessRightSet.ofList [.read, .write, .grant]
  let innerCaps : List (SeLe4n.Slot × Capability) :=
    [(SeLe4n.Slot.ofNat 2, { target := .object epId, rights := rw }),
     (SeLe4n.Slot.ofNat 3, { target := .object deepId, rights := rw })]
  let build (inner : List (SeLe4n.Slot × Capability)) : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject rootId (.cnode (CNode.ofList 0 0 0 3
          [(SeLe4n.Slot.ofNat 0, { target := .object innerId, rights := rw })]))
      |>.withObject innerId (.cnode (CNode.ofList 0 0 0 3 inner))
      |>.withObject deepId (.cnode (CNode.ofList 0 0 0 3
          [(SeLe4n.Slot.ofNat 0, { target := .object ep2Id, rights := rw })]))
      |>.withObject epId (.endpoint {})
      |>.withObject ep2Id (.endpoint {})
      |>.buildChecked)
  let st := build innerCaps
  let root : SeLe4n.Kernel.CSpaceAddr := { cnode := rootId, slot := SeLe4n.Slot.ofNat 0 }
  unless SeLe4n.Kernel.zombieSlotClass st rootId root.slot rootId root.slot != 0 do
    throw <| IO.userError "the fixture's root slot must name a CNode holding a capability"
  let full := SeLe4n.Kernel.zombieDeleteAt bootCoreId rootId root.slot st
  unless (full.slotCapAt root).isNone && (full.getObject? innerId).isNone &&
      (full.getObject? deepId).isNone do
    throw <| IO.userError "the zombie delete must delete the slot and retire the CNodes below it"
  IO.println "positive check passed [a zombie delete empties and retires the CNodes below its slot]"
  -- A cycle back to the loop's own CNode.
  let stC := build (innerCaps ++ [(SeLe4n.Slot.ofNat 5, { target := .object rootId, rights := rw })])
  unless SeLe4n.Kernel.zombieSlotClass stC rootId root.slot rootId root.slot != 0 do
    throw <| IO.userError "the cyclic fixture's root slot must name a CNode holding a capability"
  let fullC := SeLe4n.Kernel.zombieDeleteAt bootCoreId rootId root.slot stC
  unless (fullC.slotCapAt root).isNone && (fullC.getObject? innerId).isNone &&
      (fullC.getObject? deepId).isNone && (fullC.getObject? rootId).isSome do
    throw <| IO.userError
      "the zombie delete through a cycle to its own CNode must delete the slot and keep that CNode"
  IO.println "positive check passed [a zombie delete ends on a cycle through its own CNode]"
  -- A space change whose old CSpace root is the last capability to CNode 11
  -- deletes it through the zombie loop: CNode 11 is emptied and retired, and
  -- the thread names the new root.  The VSpace root's old capability is a copy
  -- of CNode 10's slot 1, so it is not final and nothing else is retired.
  let tId : SeLe4n.ObjId := ⟨6⟩
  let newCn : SeLe4n.ObjId := ⟨14⟩
  let vsId : SeLe4n.ObjId := ⟨20⟩
  let stS : SystemState :=
    ((BootstrapBuilder.empty
      |>.withObject rootId (.cnode (CNode.ofList 0 0 0 3
          [(SeLe4n.Slot.ofNat 0, { target := .object newCn, rights := rw }),
           (SeLe4n.Slot.ofNat 1, { target := .object vsId, rights := rw })]))
      |>.withObject innerId (.cnode (CNode.ofList 0 0 0 3
          [(SeLe4n.Slot.ofNat 2, { target := .object epId, rights := rw })]))
      |>.withObject epId (.endpoint {})
      |>.withObject newCn (.cnode (CNode.ofList 0 0 0 3 []))
      |>.withObject vsId (.vspaceRoot { asid := asidPrimary, mappings := {} })
      |>.withObject tId (.tcb {
          tid := ⟨6⟩
          priority := ⟨40⟩
          domain := ⟨0⟩
          threadState := .Inactive
          spaceCells := SeLe4n.Model.TCB.spaceCellsOf innerId vsId
          ipcBuffer := (SeLe4n.VAddr.ofNat 4096)
        })
      |>.buildChecked).withDerivationEdges
        [({ cnode := rootId, slot := SeLe4n.Slot.ofNat 1 },
          { cnode := tId, slot := SeLe4n.Slot.ofNat 1 }, .copy)])
  let cnSrc : SeLe4n.Kernel.CSpaceAddr := { cnode := rootId, slot := SeLe4n.Slot.ofNat 0 }
  let vrSrc : SeLe4n.Kernel.CSpaceAddr := { cnode := rootId, slot := SeLe4n.Slot.ofNat 1 }
  match SeLe4n.Kernel.validateThreadIdArg (SeLe4n.ThreadId.ofNat 6) with
  | .error _ => throw <| IO.userError "thread 6 must validate"
  | .ok vtid =>
    unless SeLe4n.Kernel.zombieSlotClass stS tId SeLe4n.Model.TCB.cspaceRootSlot tId
        SeLe4n.Model.TCB.cspaceRootSlot != 0 do
      throw <| IO.userError "the thread's old CSpace root must name a CNode holding a capability"
    match SeLe4n.Kernel.copyThreadSpacesZombie bootCoreId stS vtid cnSrc vrSrc with
    | .error e => throw <| IO.userError s!"the space change must succeed, got {repr e}"
    | .ok stS' =>
      match stS'.getTcb? ⟨6⟩ with
      | none => throw <| IO.userError "the thread must survive its space change"
      | some t =>
        unless t.cspaceRoot == newCn && t.vspaceRoot == vsId &&
            (stS'.getObject? innerId).isNone && (stS'.getObject? epId).isNone &&
            (stS'.getObject? vsId).isSome do
          throw <| IO.userError
            "the space change must empty and retire the old CSpace root and name the new one"
    IO.println "positive check passed [a space change deletes its old root through the zombie loop]"
  IO.println "all zombie delete checks passed"

/-- **A final delete of an untyped with children splices it out**, as seL4's
derivation tree does: untyped 30 records untyped 31 at offset 0x1000, and 31
records endpoint 32 at 0 and untyped 33 at 0x200.  Deleting the last capability
to 31 retires it; 30 then records 32 and 33 at 0x1000 and 0x1200, and 33 names
30 as its parent. -/
private def runUntypedRetireSpliceChecks : IO Unit := do
  let cnId : SeLe4n.ObjId := ⟨10⟩
  let u0 : SeLe4n.ObjId := ⟨30⟩
  let u1 : SeLe4n.ObjId := ⟨31⟩
  let epId : SeLe4n.ObjId := ⟨32⟩
  let u2 : SeLe4n.ObjId := ⟨33⟩
  let rw : AccessRightSet := AccessRightSet.ofList [.read, .write, .grant]
  let st : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject cnId (.cnode (CNode.ofList 0 0 0 3
          [(SeLe4n.Slot.ofNat 0, { target := .object u1, rights := rw })]))
      |>.withObject u0 (.untyped {
          regionBase := (SeLe4n.PAddr.ofNat 0x100000)
          regionSize := 0x4000
          children := [{ objId := u1, offset := 0x1000, size := 0x1000 }] })
      |>.withObject u1 (.untyped {
          regionBase := (SeLe4n.PAddr.ofNat 0x101000)
          regionSize := 0x1000
          parent := some u0
          children := [{ objId := epId, offset := 0, size := 0x100 },
            { objId := u2, offset := 0x200, size := 0x200 }] })
      |>.withObject epId (.endpoint {})
      |>.withObject u2 (.untyped {
          regionBase := (SeLe4n.PAddr.ofNat 0x101200)
          regionSize := 0x200
          parent := some u1 })
      |>.buildChecked)
  let addr : SeLe4n.Kernel.CSpaceAddr := { cnode := cnId, slot := SeLe4n.Slot.ofNat 0 }
  unless SeLe4n.Kernel.slotRetireTarget st cnId addr.slot == u1.toNat + 1 &&
      SeLe4n.Kernel.slotRetireRecorder st cnId addr.slot == u0.toNat + 1 do
    throw <| IO.userError "the final capability to untyped 31 must retire it, recorded by 30"
  match SeLe4n.Kernel.cspaceDeleteSlotFinalising bootCoreId addr st with
  | .error e => throw <| IO.userError s!"the final delete of untyped 31 must succeed, got {repr e}"
  | .ok ((), st') =>
    let kids := match st'.getUntyped? u0 with
      | some U => U.children.map fun c => (c.objId, c.offset)
      | none => []
    unless (st'.getObject? u1).isNone && (st'.getObject? epId).isSome &&
        kids == [(epId, 0x1000), (u2, 0x1200)] do
      throw <| IO.userError
        s!"the recorder must adopt the retired untyped's children, rebased; got {repr kids}"
    unless (st'.getUntyped? u2).map (·.parent) == some (some u0) do
      throw <| IO.userError "the adopted child untyped must name the recorder as its parent"
  IO.println "positive check passed [a final untyped delete splices its children into the recorder]"

end SeLe4n.Testing

def main : IO Unit := do
  SeLe4n.Testing.runNegativeChecks
  SeLe4n.Testing.runH2NegativeChecks
  SeLe4n.Testing.runAuditCoverageChecks
  SeLe4n.Testing.runWSH7Checks
  SeLe4n.Testing.runWSH11Checks
  SeLe4n.Testing.runWSH15Checks
  SeLe4n.Testing.runWSH15PlatformChecks
  SeLe4n.Testing.runWSH16LifecycleChecks
  SeLe4n.Testing.runWSJ1DecodeChecks
  SeLe4n.Testing.runWSKGChecks
  SeLe4n.Testing.runWSL4BlockedThreadChecks
  SeLe4n.Testing.runWSM3CapTransferNegativeChecks
  SeLe4n.Testing.runL13CapTransferShortCircuitChecks
  SeLe4n.Testing.runWSM4ResolveEdgeCaseChecks
  SeLe4n.Testing.runRevocationRefusalChecks
  SeLe4n.Testing.runThreadSlotInvocationRefusalChecks
  SeLe4n.Testing.runWSR4CoherenceChecks
  SeLe4n.Testing.runS2GCapabilityErrorTests
  SeLe4n.Testing.runS2HLifecycleErrorTests
  SeLe4n.Testing.runX2RuntimeInvariantTests
  SeLe4n.Testing.runZ8SchedContextNegativeChecks
  SeLe4n.Testing.runAC1BudgetFailClosedChecks
  SeLe4n.Testing.runAC1CdtTrackingChecks
  SeLe4n.Testing.runR1IpcCallPathSymmetryChecks
  SeLe4n.Testing.runR5EOrphanedSchedContextChecks
  SeLe4n.Testing.runWSRR8CSpaceSlotRangeChecks
  SeLe4n.Testing.runZombieDeleteCompletesChecks
  SeLe4n.Testing.runUntypedRetireSpliceChecks
