-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API
import SeLe4n.Kernel.Architecture.VSpace
import SeLe4n.Model.State
import SeLe4n.Testing.StateBuilder

/-!
# VSpace capability-binding suite (PR #845 review, P1)

Regression coverage for the confused-deputy defect in the VSpace syscall
dispatch arms.

## The defect

`syscallLookupCap` resolves a CPtr through the caller's CSpace and checks only
that the resolved capability carries the syscall's **required right**.  It never
tied that capability's *target* to the operand the syscall acts on.  The
`.vspaceMap` / `.vspaceUnmap` / `.vspaceUnifyInstruction` arms matched
`| .object _ =>`, discarding the object id, and then operated on an **ASID the
caller supplied in a message register**, resolved through the global
`asidTable`.

Authority therefore flowed from a name the caller chose rather than from the
capability it held.  A thread holding a writable capability to *any* object —
its own TCB — could unmap pages in an address space it had no capability for.

## The fix

`SeLe4n.Kernel.vspaceCapAuthorizesAsid` requires the capability to name the
VSpace root that `resolveAsidRoot` yields for the operand ASID, checked in each
arm before the transition runs.

## What this suite pins

Every scenario drives the **live** `dispatchSyscall` path — CSpace resolution,
rights gate, and the new binding — rather than calling the transitions directly,
because the defect lived in dispatch and only dispatch can witness it.

* §1 — surface anchors for the predicate and its fail-closed theorems.
* §2 — the predicate's own truth table on a real page-table-backed state.
* §3 — `.vspaceUnmap`: the original exploit, now refused, with the victim
  mapping proven still present.
* §4 — `.vspaceUnifyInstruction`: same, plus the no-maintenance-emitted check.
* §5 — `.vspaceMap`: same, proving no mapping is installed.
* §6 — the authorized positive paths still work (the gate is not a blanket
  denial).
-/

namespace SeLe4n.Testing.VSpaceCapabilityBinding

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Architecture

-- ============================================================================
-- §1  Surface anchors (Tier-3)
-- ============================================================================

#check @SeLe4n.Kernel.vspaceCapAuthorizesAsid
#check @SeLe4n.Kernel.vspaceCapAuthorizesAsid_iff
#check @SeLe4n.Kernel.vspaceCapAuthorizesAsid_false_of_ne
#check @SeLe4n.Kernel.vspaceCapAuthorizesAsid_false_of_unbound
#check @SeLe4n.Kernel.vspaceCapAuthorizesAsid_false_of_not_object
#check @SeLe4n.Kernel.dispatchWithCap_vspaceMap_unauthorized
#check @SeLe4n.Kernel.dispatchWithCap_vspaceUnmap_unauthorized
#check @SeLe4n.Kernel.dispatchWithCap_vspaceUnifyInstruction_unauthorized
#check @SeLe4n.Kernel.dispatchWithCap_vspaceMap_delegates
#check @SeLe4n.Kernel.dispatchWithCap_vspaceUnmap_delegates
#check @SeLe4n.Kernel.dispatchWithCap_vspaceUnifyInstruction_delegates

-- ============================================================================
-- Scenario fixture
-- ============================================================================

private def victimVsp   : SeLe4n.ObjId    := ⟨900⟩
private def attackerVsp : SeLe4n.ObjId    := ⟨901⟩
private def attackerCn  : SeLe4n.ObjId    := ⟨902⟩
private def attacker    : SeLe4n.ThreadId := ⟨903⟩

private def victimAsid   : SeLe4n.ASID := SeLe4n.ASID.ofNat 7
private def attackerAsid : SeLe4n.ASID := SeLe4n.ASID.ofNat 5
private def unboundAsid  : SeLe4n.ASID := SeLe4n.ASID.ofNat 9

private def victimVaddr : SeLe4n.VAddr := SeLe4n.VAddr.ofNat 0x40000
private def victimPaddr : SeLe4n.PAddr := SeLe4n.PAddr.ofNat 0x90000
private def freshVaddr  : SeLe4n.VAddr := SeLe4n.VAddr.ofNat 0x50000

private def execPerms : PagePermissions :=
  { read := true, write := false, execute := true, user := true, cacheable := true }

/-- A writable capability to the attacker's **own TCB** — an object with no
relationship to any address space.  This is the capability the original exploit
used. -/
private def unrelatedCap : Capability :=
  { target := .object attacker.toObjId,
    rights := AccessRightSet.ofList [.read, .write] }

/-- A writable capability to the attacker's *own* VSpace root — legitimate
authority, but over the wrong address space. -/
private def ownRootCap : Capability :=
  { target := .object attackerVsp,
    rights := AccessRightSet.ofList [.read, .write] }

/-- A writable capability to the **victim's** VSpace root — genuine authority. -/
private def victimRootCap : Capability :=
  { target := .object victimVsp,
    rights := AccessRightSet.ofList [.read, .write] }

/-- Build the scenario with `cap` in the attacker's CSpace at slot 0, and an
executable page already mapped in the *victim's* address space. -/
private def scenario (cap : Capability) : Option SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject victimVsp (.vspaceRoot { asid := victimAsid, mappings := {} })
      |>.withObject attackerVsp (.vspaceRoot { asid := attackerAsid, mappings := {} })
      |>.withObject attackerCn (.cnode
          { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
            slots := SeLe4n.UniqueSlotMap.ofListWF [(SeLe4n.Slot.ofNat 0, cap)] })
      |>.withObject attacker.toObjId (.tcb
          { tid := attacker, priority := ⟨40⟩, domain := ⟨0⟩,
            cspaceRoot := attackerCn, vspaceRoot := attackerVsp,
            ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready })
      |>.withRunnable [attacker]
      |>.build)
  match vspaceMapPageWithFlush victimAsid victimVaddr victimPaddr execPerms base with
  | .ok ((), s) => some s
  | .error _    => none

/-- Two-register decode (asid, vaddr) — the `.vspaceUnmap` /
`.vspaceUnifyInstruction` operand shape. -/
private def decode2 (sid : SeLe4n.Model.SyscallId) (asid vaddr : Nat) :
    SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat 0
  , msgInfo   := { length := 2, extraCaps := 0, label := 0 }
  , syscallId := sid
  , msgRegs   := #[SeLe4n.RegValue.ofNat asid, SeLe4n.RegValue.ofNat vaddr] }

/-- Four-register decode (asid, vaddr, paddr, perms) — the `.vspaceMap` shape.
Permissions `0b11001` = read + user + cacheable (W^X-compliant). -/
private def decodeMap (asid vaddr paddr : Nat) : SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat 0
  , msgInfo   := { length := 4, extraCaps := 0, label := 0 }
  , syscallId := .vspaceMap
  , msgRegs   := #[SeLe4n.RegValue.ofNat asid, SeLe4n.RegValue.ofNat vaddr,
                   SeLe4n.RegValue.ofNat paddr, SeLe4n.RegValue.ofNat 25] }

private def assertBool (label : String) (b : Bool) : IO Unit :=
  if b then IO.println s!"  PASS: {label}"
  else throw (IO.userError s!"  FAIL: {label}")

/-- Is `vaddr` still mapped in the address space bound to `asid`? -/
private def stillMapped (st : SystemState) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) : Bool :=
  match resolveAsidRoot st asid with
  | some (_, root) => (VSpaceRoot.lookup root vaddr).isSome
  | none           => false

private def isIllegalAuthority (r : Except KernelError (Unit × SystemState)) : Bool :=
  match r with
  | .error .illegalAuthority => true
  | _                        => false

-- ============================================================================
-- §2  The predicate's truth table on a real page-table-backed state
-- ============================================================================

private def runPredicateChecks : IO Unit := do
  IO.println "-- §2 vspaceCapAuthorizesAsid truth table"
  match scenario victimRootCap with
  | none => assertBool "the scenario builds" false
  | some st => do
    assertBool "a cap naming the operand ASID's root AUTHORIZES"
      (vspaceCapAuthorizesAsid victimRootCap victimAsid st)
    assertBool "a cap naming a DIFFERENT VSpace root does not"
      (!(vspaceCapAuthorizesAsid ownRootCap victimAsid st))
    assertBool "a cap naming an unrelated object (a TCB) does not"
      (!(vspaceCapAuthorizesAsid unrelatedCap victimAsid st))
    assertBool "no capability authorizes an UNBOUND ASID (fail-closed)"
      ([unrelatedCap, ownRootCap, victimRootCap].all
        fun c => !(vspaceCapAuthorizesAsid c unboundAsid st))
    assertBool "each root's own cap authorizes its own ASID"
      (vspaceCapAuthorizesAsid ownRootCap attackerAsid st &&
       vspaceCapAuthorizesAsid victimRootCap victimAsid st)

-- ============================================================================
-- §3  `.vspaceUnmap` — the original exploit, now refused
-- ============================================================================

private def runUnmapBindingChecks : IO Unit := do
  IO.println "-- §3 `.vspaceUnmap` capability binding"
  let d := decode2 .vspaceUnmap 7 0x40000
  -- The exploit: a writable cap to the attacker's OWN TCB, naming the victim's
  -- address space.  Before the fix this unmapped the victim's page.
  match scenario unrelatedCap with
  | none => assertBool "the exploit scenario builds" false
  | some st => do
    assertBool "the victim's page is mapped before the attempt"
      (stillMapped st victimAsid victimVaddr)
    let r := dispatchSyscall d attacker st
    assertBool "an unrelated writable cap is REFUSED (illegalAuthority)"
      (isIllegalAuthority r)
    assertBool "and the victim's mapping survives"
      (match r with
        | .error _ => stillMapped st victimAsid victimVaddr
        | .ok ((), st') => stillMapped st' victimAsid victimVaddr)
  -- Legitimate authority over the WRONG address space is equally refused.
  match scenario ownRootCap with
  | none => assertBool "the wrong-root scenario builds" false
  | some st =>
    assertBool "a cap to the caller's OWN VSpace root is refused for another ASID"
      (isIllegalAuthority (dispatchSyscall d attacker st))
  -- Fail-closed on an unbound ASID: no ASID-existence oracle.
  match scenario victimRootCap with
  | none => assertBool "the unbound-ASID scenario builds" false
  | some st =>
    assertBool "an UNBOUND ASID is refused with illegalAuthority (no oracle)"
      (isIllegalAuthority (dispatchSyscall (decode2 .vspaceUnmap 9 0x40000) attacker st))

-- ============================================================================
-- §4  `.vspaceUnifyInstruction` — cache maintenance cannot probe another AS
-- ============================================================================

private def runUnifyBindingChecks : IO Unit := do
  IO.println "-- §4 `.vspaceUnifyInstruction` capability binding"
  let d := decode2 .vspaceUnifyInstruction 7 0x40000
  match scenario unrelatedCap with
  | none => assertBool "the exploit scenario builds" false
  | some st => do
    let r := dispatchSyscall d attacker st
    assertBool "an unrelated writable cap is REFUSED (illegalAuthority)"
      (isIllegalAuthority r)
    assertBool "and NO cache maintenance is emitted for the victim's page"
      (match r with
        | .error _ => st.pendingIcacheMaintenance == []
        | .ok ((), st') => st'.pendingIcacheMaintenance == [])
  match scenario ownRootCap with
  | none => assertBool "the wrong-root scenario builds" false
  | some st =>
    assertBool "a cap to the caller's OWN VSpace root is refused for another ASID"
      (isIllegalAuthority (dispatchSyscall d attacker st))
  match scenario victimRootCap with
  | none => assertBool "the unbound-ASID scenario builds" false
  | some st =>
    assertBool "an UNBOUND ASID is refused with illegalAuthority (no oracle)"
      (isIllegalAuthority
        (dispatchSyscall (decode2 .vspaceUnifyInstruction 9 0x40000) attacker st))

-- ============================================================================
-- §5  `.vspaceMap` — no mapping is installed into another address space
-- ============================================================================

private def runMapBindingChecks : IO Unit := do
  IO.println "-- §5 `.vspaceMap` capability binding"
  let d := decodeMap 7 0x50000 0xA0000
  match scenario unrelatedCap with
  | none => assertBool "the exploit scenario builds" false
  | some st => do
    assertBool "the target vaddr is unmapped in the victim's AS beforehand"
      (!(stillMapped st victimAsid freshVaddr))
    let r := dispatchSyscall d attacker st
    assertBool "an unrelated writable cap is REFUSED (illegalAuthority)"
      (isIllegalAuthority r)
    assertBool "and NO mapping is installed in the victim's address space"
      (match r with
        | .error _ => !(stillMapped st victimAsid freshVaddr)
        | .ok ((), st') => !(stillMapped st' victimAsid freshVaddr))
  match scenario ownRootCap with
  | none => assertBool "the wrong-root scenario builds" false
  | some st =>
    assertBool "a cap to the caller's OWN VSpace root is refused for another ASID"
      (isIllegalAuthority (dispatchSyscall d attacker st))
  match scenario victimRootCap with
  | none => assertBool "the unbound-ASID scenario builds" false
  | some st =>
    assertBool "an UNBOUND ASID is refused with illegalAuthority (no oracle)"
      (isIllegalAuthority (dispatchSyscall (decodeMap 9 0x50000 0xA0000) attacker st))

-- ============================================================================
-- §6  The authorized paths still work — the gate is not a blanket denial
-- ============================================================================

private def runAuthorizedChecks : IO Unit := do
  IO.println "-- §6 authorized callers still succeed"
  -- `.vspaceUnmap` with genuine authority over the victim's address space.
  match scenario victimRootCap with
  | none => assertBool "the authorized scenario builds" false
  | some st => do
    match dispatchSyscall (decode2 .vspaceUnmap 7 0x40000) attacker st with
    | .error _ => assertBool "authorized `.vspaceUnmap` succeeds" false
    | .ok ((), st') => do
      assertBool "authorized `.vspaceUnmap` succeeds"
        true
      assertBool "and the mapping is actually removed"
        (!(stillMapped st' victimAsid victimVaddr))
    -- `.vspaceUnifyInstruction` with the same authority.
    match dispatchSyscall (decode2 .vspaceUnifyInstruction 7 0x40000) attacker st with
    | .error _ => assertBool "authorized `.vspaceUnifyInstruction` succeeds" false
    | .ok ((), st') => do
      assertBool "authorized `.vspaceUnifyInstruction` succeeds" true
      assertBool "and records the unify operand for the victim's page"
        (st'.pendingIcacheMaintenance == [ICacheInvalidation.unifyPage victimPaddr])
    -- `.vspaceMap` into the address space the capability names.
    match dispatchSyscall (decodeMap 7 0x50000 0xA0000) attacker st with
    | .error _ => assertBool "authorized `.vspaceMap` succeeds" false
    | .ok ((), st') => do
      assertBool "authorized `.vspaceMap` succeeds" true
      assertBool "and the new mapping is installed"
        (stillMapped st' victimAsid freshVaddr)
  -- A caller acting on its OWN address space with its own root capability.
  match scenario ownRootCap with
  | none => assertBool "the own-AS scenario builds" false
  | some st =>
    assertBool "a caller may map into its OWN address space with its own root cap"
      (match dispatchSyscall (decodeMap 5 0x50000 0xA0000) attacker st with
        | .ok ((), st') => stillMapped st' attackerAsid freshVaddr
        | .error _ => false)

def runVSpaceCapabilityBindingChecks : IO Unit := do
  IO.println "===================================================="
  IO.println "VSpace capability-binding suite (PR #845 review, P1)"
  IO.println "===================================================="
  runPredicateChecks
  runUnmapBindingChecks
  runUnifyBindingChecks
  runMapBindingChecks
  runAuthorizedChecks
  IO.println "===================================================="
  IO.println "All VSpace capability-binding checks PASS."

end SeLe4n.Testing.VSpaceCapabilityBinding

def main : IO Unit :=
  SeLe4n.Testing.VSpaceCapabilityBinding.runVSpaceCapabilityBindingChecks
