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
* §5b — physical-address alignment, now of a frame's own `base`.
* §5c — **WS-BP BP7.1: authority over the address space is not authority over
  the memory.**  `.vspaceMap`'s MR2 names a frame *capability*; the page mapped
  is that frame's `base`, never a register value.  The retired reading — MR2 as
  a raw physical address — is refused, and every other way to name memory
  without holding it is too.
* §5d — **WS-BP BP7.1 (`v0.36.5`): memory reaches a thread only by a carve.**
  `.untypedRetype` mints a frame out of an untyped the caller holds, at the
  untyped's watermark, zeroed if it is RAM; `.vspaceMap` then maps exactly that
  page.  Every refusal the carve owns is exercised.
* §5e — **WS-BP BP7.1 (`v0.36.6`): memory returns to its untyped.**
  `.untypedReset` refuses while any capability names a carved frame — including
  one reached only through a **sibling copy** of the untyped capability, which a
  per-slot "no derivations" test would miss — and after `.cspaceRevoke` it
  removes every mapping of the region (an unrelated mapping survives), retires
  the frames and resets the watermark, so the next carve reuses both the page,
  zeroed again, and the child id.
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
#check @SeLe4n.Kernel.resolveVSpaceMapFrame_ok_authorised
#check @SeLe4n.Kernel.vspaceMapFromFrameCap_ok
#check @SeLe4n.Kernel.dispatchWithCap_vspaceMap_requires_frame_cap
#check @SeLe4n.Kernel.dispatchWithCap_vspaceMap_maps_frame_base
#check @SeLe4n.Kernel.frameMappingAdmissible_write
#check @SeLe4n.Kernel.frameMappingAdmissible_device
#check @SeLe4n.Kernel.untypedRetypeFrame
#check @SeLe4n.Kernel.untypedRetypeFrame_ok_decompose
#check @SeLe4n.Kernel.untypedRetypeFrame_ok_frame
#check @SeLe4n.Kernel.untypedNextFrame_of_retype_ok
#check @SeLe4n.Kernel.untypedRetypeFromCap_ok
#check @SeLe4n.Kernel.untypedRetypeFrame_preserves_ipcInvariantFull

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

-- WS-BP BP7.1: the frames the attacker's CSpace holds capabilities to.  A
-- mapping names one of these by capability; its address is the frame's `base`.
private def frameA   : SeLe4n.ObjId := ⟨910⟩  -- ordinary memory at 0xA0000
private def frameDev : SeLe4n.ObjId := ⟨911⟩  -- a device page at 0xB0000
private def frameOdd : SeLe4n.ObjId := ⟨912⟩  -- an unaligned base (defence in depth)
private def frameABase : Nat := 0xA0000

private def frameCapTo (f : SeLe4n.ObjId) (rs : List AccessRight) : Capability :=
  { target := .object f, rights := AccessRightSet.ofList rs }

/-- The attacker's CSpace slots beside the capability under test at slot 0. -/
private def slotFrameRO     : Nat := 1  -- read-only cap to frame A
private def slotFrameRW     : Nat := 2  -- read-write cap to frame A
private def slotFrameNoRead : Nat := 3  -- write-only cap to frame A (no `.read`)
private def slotFrameDev    : Nat := 4  -- read-only cap to the device frame
private def slotFrameOdd    : Nat := 5  -- read-only cap to the unaligned frame
private def slotNotFrame    : Nat := 6  -- a readable cap to a non-frame (the attacker's TCB)
private def slotEmpty       : Nat := 7  -- nothing

/-- Build the scenario with `cap` in the attacker's CSpace at slot 0, frame
capabilities at slots 1–6 (WS-BP BP7.1), and an executable page already mapped
in the *victim's* address space. -/
private def scenario (cap : Capability) : Option SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject victimVsp (.vspaceRoot { asid := victimAsid, mappings := {} })
      |>.withObject attackerVsp (.vspaceRoot { asid := attackerAsid, mappings := {} })
      |>.withObject frameA (.frame { base := SeLe4n.PAddr.ofNat frameABase })
      |>.withObject frameDev (.frame { base := SeLe4n.PAddr.ofNat 0xB0000, isDevice := true })
      |>.withObject frameOdd (.frame { base := SeLe4n.PAddr.ofNat 0xA0001 })
      |>.withObject attackerCn (.cnode
          { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
            slots := SeLe4n.UniqueSlotMap.ofListWF
              [(SeLe4n.Slot.ofNat 0, cap),
               (SeLe4n.Slot.ofNat slotFrameRO, frameCapTo frameA [.read]),
               (SeLe4n.Slot.ofNat slotFrameRW, frameCapTo frameA [.read, .write]),
               (SeLe4n.Slot.ofNat slotFrameNoRead, frameCapTo frameA [.write]),
               (SeLe4n.Slot.ofNat slotFrameDev, frameCapTo frameDev [.read]),
               (SeLe4n.Slot.ofNat slotFrameOdd, frameCapTo frameOdd [.read]),
               (SeLe4n.Slot.ofNat slotNotFrame, frameCapTo attacker.toObjId [.read])] })
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

/-- Permission words (bit 0 read, 1 write, 2 execute, 3 user, 4 cacheable). -/
private def permsRUC  : Nat := 25  -- read + user + cacheable (W^X-compliant)
private def permsRWUC : Nat := 27  -- read + write + user + cacheable
private def permsRXU  : Nat := 13  -- read + execute + user (uncached)
private def permsRU   : Nat := 9   -- read + user (uncached, non-executable)

/-- Four-register decode (asid, vaddr, frame capability address, perms) — the
`.vspaceMap` shape.  WS-BP BP7.1: MR2 is the address of a **frame capability**
in the caller's CSpace, never a physical address. -/
private def decodeMap (asid vaddr frameSlot : Nat) (perms : Nat := permsRUC) :
    SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat 0
  , msgInfo   := { length := 4, extraCaps := 0, label := 0 }
  , syscallId := .vspaceMap
  , msgRegs   := #[SeLe4n.RegValue.ofNat asid, SeLe4n.RegValue.ofNat vaddr,
                   SeLe4n.RegValue.ofNat frameSlot, SeLe4n.RegValue.ofNat perms] }

/-- The physical address `vaddr` translates to in the address space bound to
`asid`, if any. -/
private def mappedPaddr (st : SystemState) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) : Option Nat :=
  match resolveAsidRoot st asid with
  | some (_, root) => (VSpaceRoot.lookup root vaddr).map (fun p => p.1.toNat)
  | none           => none

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
  let d := decodeMap 7 0x50000 slotFrameRO
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
      (isIllegalAuthority (dispatchSyscall (decodeMap 9 0x50000 slotFrameRO) attacker st))

-- ============================================================================
-- §6  The authorized paths still work — the gate is not a blanket denial
-- ============================================================================

-- ============================================================================
-- §5b  Physical-address page alignment (PR #845 review, P2)
-- ============================================================================

/-- **PR #845 review (P2)**: a page mapping's physical address must be page
aligned.  WS-BP BP7.1: that address is a frame's own `base`; the kernel never
builds an unaligned frame (`FrameObject.wellFormed`), so the unaligned frame
here is planted by the fixture and the map wrapper's guard is the defence in
depth that still refuses it.  ARMv8 page descriptors carry only the aligned base
(`PageTable.descriptorToUInt64` masks the low bits) and both HAL cache
maintenance loops round their operand down to the containing page — so
accepting an unaligned PA and silently rounding would make the model's recorded
`.ivauPage` / `.unifyPage` operand name a different address than the one
hardware acts on.  `vspaceMapPageChecked` now rejects it structurally. -/
private def runAlignmentChecks : IO Unit := do
  IO.println "-- §5b physical-address page alignment"
  match scenario victimRootCap with
  | none => assertBool "the alignment scenario builds" false
  | some st => do
    -- One byte past a page boundary: rejected, and nothing is installed.
    let r := dispatchSyscall (decodeMap 7 0x50000 slotFrameOdd) attacker st
    assertBool "an unaligned PA is refused (alignmentError)"
      (match r with | .error .alignmentError => true | _ => false)
    assertBool "and no mapping is installed for it"
      (match r with
        | .error _ => !(stillMapped st victimAsid freshVaddr)
        | .ok ((), st') => !(stillMapped st' victimAsid freshVaddr))
    -- The aligned neighbour of the same page succeeds, so the guard rejects
    -- exactly misalignment rather than the address range.
    assertBool "the page-aligned base of the same page is accepted"
      (match dispatchSyscall (decodeMap 7 0x50000 slotFrameRO) attacker st with
        | .ok ((), st') => stillMapped st' victimAsid freshVaddr
        | .error _ => false)
    -- The guard is authority-independent: an unauthorized caller is still
    -- refused for *authority*, not alignment (the binding runs first).
    match scenario unrelatedCap with
    | none => assertBool "the unauthorized-alignment scenario builds" false
    | some stU =>
      assertBool "authority is checked before alignment (illegalAuthority wins)"
        (match dispatchSyscall (decodeMap 7 0x50000 slotFrameOdd) attacker stU with
          | .error .illegalAuthority => true | _ => false)

-- ============================================================================
-- §5c  WS-BP BP7.1 — authority over the address space is not authority over
--      the memory
-- ============================================================================

/-- The caller here holds the **victim's own VSpace root capability** — full
authority over that address space, which is exactly what PR #845's binding asks
for — and every check below is still refused unless MR2 names a frame the caller
holds.  Before `v0.36.4` MR2 was a raw physical address: that one capability was
authority over every page of physical memory, the kernel image included. -/
private def runFrameCapabilityChecks : IO Unit := do
  IO.println "-- §5c `.vspaceMap` maps a frame the caller HOLDS (WS-BP BP7.1)"
  match scenario victimRootCap with
  | none => assertBool "the frame-capability scenario builds" false
  | some st => do
    let isErr (e : KernelError) (r : Except KernelError (Unit × SystemState)) : Bool :=
      match r with | .error e' => e' == e | .ok _ => false
    let nothingMapped (r : Except KernelError (Unit × SystemState)) : Bool :=
      match r with
      | .error _ => !(stillMapped st victimAsid freshVaddr)
      | .ok ((), st') => !(stillMapped st' victimAsid freshVaddr)
    -- The retired reading: MR2 as the raw physical address of the frame's page.
    -- `0xA0000` is a CSpace *address* now; it masks to slot 0, which holds a
    -- VSpace-root capability, not a frame — refused, and nothing is mapped.
    let rRaw := dispatchSyscall (decodeMap 7 0x50000 frameABase) attacker st
    assertBool "the RETIRED reading (MR2 = a raw physical address) maps nothing"
      (isErr .invalidCapability rRaw && nothingMapped rRaw)
    -- Naming memory without holding a frame capability, every other way.
    let rNotFrame := dispatchSyscall (decodeMap 7 0x50000 slotNotFrame) attacker st
    assertBool "a capability to a non-frame object is refused (invalidCapability)"
      (isErr .invalidCapability rNotFrame && nothingMapped rNotFrame)
    let rEmpty := dispatchSyscall (decodeMap 7 0x50000 slotEmpty) attacker st
    assertBool "an empty CSpace slot is refused (invalidCapability)"
      (isErr .invalidCapability rEmpty && nothingMapped rEmpty)
    let rNoRead := dispatchSyscall (decodeMap 7 0x50000 slotFrameNoRead) attacker st
    assertBool "a frame capability without `.read` is refused (illegalAuthority)"
      (isErr .illegalAuthority rNoRead && nothingMapped rNoRead)
    -- The capability bounds the mapping's access.
    let rWriteRO := dispatchSyscall (decodeMap 7 0x50000 slotFrameRO permsRWUC) attacker st
    assertBool "a WRITABLE mapping through a read-only frame cap is refused (illegalAuthority)"
      (isErr .illegalAuthority rWriteRO && nothingMapped rWriteRO)
    assertBool "a writable mapping through a read-write frame cap is installed"
      (match dispatchSyscall (decodeMap 7 0x50000 slotFrameRW permsRWUC) attacker st with
        | .ok ((), st') => mappedPaddr st' victimAsid freshVaddr == some frameABase
        | .error _ => false)
    -- A device frame is mapped neither executable nor cacheable.
    let rDevX := dispatchSyscall (decodeMap 7 0x50000 slotFrameDev permsRXU) attacker st
    assertBool "an EXECUTABLE mapping of a device frame is refused (policyDenied)"
      (isErr .policyDenied rDevX && nothingMapped rDevX)
    let rDevC := dispatchSyscall (decodeMap 7 0x50000 slotFrameDev permsRUC) attacker st
    assertBool "a CACHEABLE mapping of a device frame is refused (policyDenied)"
      (isErr .policyDenied rDevC && nothingMapped rDevC)
    assertBool "an uncached, non-executable mapping of a device frame is installed"
      (match dispatchSyscall (decodeMap 7 0x50000 slotFrameDev permsRU) attacker st with
        | .ok ((), st') => mappedPaddr st' victimAsid freshVaddr == some 0xB0000
        | .error _ => false)
    -- The address mapped is the frame's own, and nothing the caller wrote.
    assertBool "the page mapped is the frame's `base`, not a register value"
      (match dispatchSyscall (decodeMap 7 0x50000 slotFrameRO) attacker st with
        | .ok ((), st') => mappedPaddr st' victimAsid freshVaddr == some frameABase
        | .error _ => false)
  -- The address-space binding still runs first: an unrelated capability is
  -- refused for AUTHORITY even when MR2 names a frame the caller holds.
  match scenario unrelatedCap with
  | none => assertBool "the unrelated-cap frame scenario builds" false
  | some stU =>
    assertBool "a held frame does not substitute for address-space authority"
      (match dispatchSyscall (decodeMap 7 0x50000 slotFrameRO) attacker stU with
        | .error .illegalAuthority => true | _ => false)

-- ============================================================================
-- §5d  WS-BP BP7.1 (`v0.36.5`) — memory reaches a thread only by a carve
-- ============================================================================

/-! The owner holds an untyped (RAM, three pages at `0x200000`), a device
untyped (one page at `0x300000`), a writable capability to its own CSpace root,
and its own VSpace root.  `.untypedRetype` is driven through the live
`dispatchSyscall`, and the frame it mints is then mapped by `.vspaceMap` — the
end-to-end path that did not exist before this version, when no reachable state
held a frame at all. -/

private def carveOwner   : SeLe4n.ThreadId := ⟨940⟩
private def carveCn      : SeLe4n.ObjId    := ⟨941⟩
private def carveVsp     : SeLe4n.ObjId    := ⟨942⟩
private def carveUt      : SeLe4n.ObjId    := ⟨943⟩
private def carveDevUt   : SeLe4n.ObjId    := ⟨944⟩
private def carveAsid    : SeLe4n.ASID     := SeLe4n.ASID.ofNat 6
private def carveUtBase  : Nat := 0x200000
private def carveDevBase : Nat := 0x300000

/-- The owner's CSpace slots. -/
private def slotUtRetype  : Nat := 0   -- the untyped, with `.retype`
private def slotOwnCnRW   : Nat := 1   -- a writable capability to the CSpace root itself
private def slotOwnVsp    : Nat := 2   -- the owner's VSpace root
private def slotUtNoRetype : Nat := 3  -- the untyped, WITHOUT `.retype`
private def slotDevUt     : Nat := 4   -- the device untyped, with `.retype`
private def slotOwnCnRO   : Nat := 5   -- a read-only capability to the CSpace root
private def slotVspRetype : Nat := 6   -- a `.retype`-bearing capability to a NON-untyped
private def slotOwnCnGrant : Nat := 7  -- a grant-bearing capability to the CSpace root (§5e copies)
private def slotCarved    : Nat := 8   -- where each carve installs its frame capability

/-- The carve scenario, with one non-zero byte at each untyped's base so the
scrub — and its absence on a device page — is observable. -/
private def carveScenario : SystemState :=
  let st :=
    (BootstrapBuilder.empty
      |>.withObject carveVsp (.vspaceRoot { asid := carveAsid, mappings := {} })
      |>.withObject carveUt (.untyped
          { regionBase := SeLe4n.PAddr.ofNat carveUtBase, regionSize := 0x3000 })
      |>.withObject carveDevUt (.untyped
          { regionBase := SeLe4n.PAddr.ofNat carveDevBase, regionSize := 0x1000,
            isDevice := true })
      |>.withObject carveCn (.cnode
          { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
            slots := SeLe4n.UniqueSlotMap.ofListWF
              [(SeLe4n.Slot.ofNat slotUtRetype, frameCapTo carveUt [.read, .write, .retype]),
               (SeLe4n.Slot.ofNat slotOwnCnRW, frameCapTo carveCn [.read, .write]),
               (SeLe4n.Slot.ofNat slotOwnVsp, frameCapTo carveVsp [.read, .write]),
               (SeLe4n.Slot.ofNat slotUtNoRetype, frameCapTo carveUt [.read, .write]),
               (SeLe4n.Slot.ofNat slotDevUt, frameCapTo carveDevUt [.read, .write, .retype]),
               (SeLe4n.Slot.ofNat slotOwnCnRO, frameCapTo carveCn [.read]),
               (SeLe4n.Slot.ofNat slotVspRetype, frameCapTo carveVsp [.read, .retype]),
               (SeLe4n.Slot.ofNat slotOwnCnGrant, frameCapTo carveCn [.read, .write, .grant])] })
      |>.withObject carveOwner.toObjId (.tcb
          { tid := carveOwner, priority := ⟨40⟩, domain := ⟨0⟩,
            cspaceRoot := carveCn, vspaceRoot := carveVsp,
            ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready })
      |>.withRunnable [carveOwner]
      |>.build)
  let m1 := SeLe4n.writeMem st.machine (SeLe4n.PAddr.ofNat carveUtBase) 0xAB
  { st with machine := SeLe4n.writeMem m1 (SeLe4n.PAddr.ofNat carveDevBase) 0xCD }

/-- Four-register decode (type tag, child id, destination CNode capability
address, destination slot), invoked on the capability at `utSlot`. -/
private def decodeCarve (utSlot tag child dstCn dstSlot : Nat) : SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat utSlot
  , msgInfo   := { length := 4, extraCaps := 0, label := 0 }
  , syscallId := .untypedRetype
  , msgRegs   := #[SeLe4n.RegValue.ofNat tag, SeLe4n.RegValue.ofNat child,
                   SeLe4n.RegValue.ofNat dstCn, SeLe4n.RegValue.ofNat dstSlot] }

private def frameTag : Nat := 8

/-- The frame at `oid`, if one is stored there. -/
private def frameAt (st : SystemState) (oid : Nat) : Option FrameObject :=
  st.getFrame? (SeLe4n.ObjId.ofNat oid)

/-- The untyped's watermark. -/
private def watermarkOf (st : SystemState) (oid : SeLe4n.ObjId) : Option Nat :=
  (st.getUntyped? oid).map (·.watermark)

/-- Four-register `.vspaceMap` decode invoked on the owner's VSpace root. -/
private def decodeOwnMap (vaddr frameSlot perms : Nat) : SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat slotOwnVsp
  , msgInfo   := { length := 4, extraCaps := 0, label := 0 }
  , syscallId := .vspaceMap
  , msgRegs   := #[SeLe4n.RegValue.ofNat 6, SeLe4n.RegValue.ofNat vaddr,
                   SeLe4n.RegValue.ofNat frameSlot, SeLe4n.RegValue.ofNat perms] }

private def runCarveChecks : IO Unit := do
  IO.println "-- §5d `.untypedRetype` carves a frame, and `.vspaceMap` maps it (WS-BP BP7.1)"
  let st := carveScenario
  let isErr (e : KernelError) (r : Except KernelError (Unit × SystemState)) : Bool :=
    match r with | .error e' => e' == e | .ok _ => false
  assertBool "the RAM page holds a non-zero byte before the carve"
    (SeLe4n.readMem st.machine (SeLe4n.PAddr.ofNat carveUtBase) == 0xAB)
  match dispatchSyscall (decodeCarve slotUtRetype frameTag 950 slotOwnCnRW slotCarved)
      carveOwner st with
  | .error e => assertBool s!"the carve succeeds (got {repr e})" false
  | .ok ((), st1) => do
    assertBool "the carve stores a frame at the child id, at the untyped's watermark"
      (frameAt st1 950 == some { base := SeLe4n.PAddr.ofNat carveUtBase })
    assertBool "the untyped's watermark advances by exactly one page"
      (watermarkOf st1 carveUt == some SeLe4n.pageBytes)
    assertBool "the carved RAM page is zeroed before any capability to it exists"
      (SeLe4n.readMem st1.machine (SeLe4n.PAddr.ofNat carveUtBase) == 0)
    assertBool "the destination slot holds a read/write/grant capability to the frame"
      (SystemState.lookupSlotCap st1 { cnode := carveCn, slot := SeLe4n.Slot.ofNat slotCarved }
        == some (frameCapability (SeLe4n.ObjId.ofNat 950)))
    -- The capability the carve handed back is authority over exactly that page.
    match dispatchSyscall (decodeOwnMap 0x60000 slotCarved permsRWUC) carveOwner st1 with
    | .error e => assertBool s!"the carved frame maps (got {repr e})" false
    | .ok ((), st2) =>
      assertBool "and `.vspaceMap` maps the CARVED page, writable"
        (mappedPaddr st2 carveAsid (SeLe4n.VAddr.ofNat 0x60000) == some carveUtBase)
    -- A second carve takes the NEXT page, never the same one.
    match dispatchSyscall (decodeCarve slotUtRetype frameTag 951 slotOwnCnRW 9)
        carveOwner st1 with
    | .error e => assertBool s!"a second carve succeeds (got {repr e})" false
    | .ok ((), st3) =>
      assertBool "a second carve takes the next page of the untyped"
        (frameAt st3 951 == some { base := SeLe4n.PAddr.ofNat (carveUtBase + SeLe4n.pageBytes) })
    -- The child id is now taken; reusing it is refused.
    assertBool "reusing a child id that holds an object is refused (childIdCollision)"
      (isErr .childIdCollision
        (dispatchSyscall (decodeCarve slotUtRetype frameTag 950 slotOwnCnRW 9) carveOwner st1))
  -- A device untyped yields a DEVICE frame, which is left unscrubbed.
  match dispatchSyscall (decodeCarve slotDevUt frameTag 952 slotOwnCnRW slotCarved)
      carveOwner st with
  | .error e => assertBool s!"a device carve succeeds (got {repr e})" false
  | .ok ((), stD) =>
    assertBool "a device untyped yields a device frame at its base"
      (frameAt stD 952 == some { base := SeLe4n.PAddr.ofNat carveDevBase, isDevice := true })
    assertBool "and a device page is NOT scrubbed (a store to MMIO is a command, not a scrub)"
      (SeLe4n.readMem stD.machine (SeLe4n.PAddr.ofNat carveDevBase) == 0xCD)
  -- Every refusal leaves the untyped and the store untouched.
  let refused (r : Except KernelError (Unit × SystemState)) : Bool :=
    match r with | .error _ => true | .ok _ => false
  assertBool "an untyped capability WITHOUT `.retype` is refused (illegalAuthority)"
    (isErr .illegalAuthority
      (dispatchSyscall (decodeCarve slotUtNoRetype frameTag 953 slotOwnCnRW slotCarved)
        carveOwner st))
  assertBool "a non-frame type is refused (invalidArgument) — kernel objects are the in-place retype's"
    (isErr .invalidArgument
      (dispatchSyscall (decodeCarve slotUtRetype 1 953 slotOwnCnRW slotCarved) carveOwner st))
  assertBool "an unknown type tag is refused (invalidTypeTag)"
    (isErr .invalidTypeTag
      (dispatchSyscall (decodeCarve slotUtRetype 9 953 slotOwnCnRW slotCarved) carveOwner st))
  assertBool "a destination CNode capability without `.write` is refused (illegalAuthority)"
    (isErr .illegalAuthority
      (dispatchSyscall (decodeCarve slotUtRetype frameTag 953 slotOwnCnRO slotCarved)
        carveOwner st))
  assertBool "an occupied destination slot is refused (targetSlotOccupied)"
    (isErr .targetSlotOccupied
      (dispatchSyscall (decodeCarve slotUtRetype frameTag 953 slotOwnCnRW slotOwnVsp)
        carveOwner st))
  assertBool "a child id that already holds an object is refused (childIdCollision)"
    (isErr .childIdCollision
      (dispatchSyscall (decodeCarve slotUtRetype frameTag carveVsp.toNat slotOwnCnRW slotCarved)
        carveOwner st))
  assertBool "the reserved sentinel as a child id is refused (invalidArgument)"
    (isErr .invalidArgument
      (dispatchSyscall (decodeCarve slotUtRetype frameTag 0 slotOwnCnRW slotCarved)
        carveOwner st))
  assertBool "a `.retype` capability to a non-untyped object is refused (untypedTypeMismatch)"
    (isErr .untypedTypeMismatch
      (dispatchSyscall (decodeCarve slotVspRetype frameTag 953 slotOwnCnRW slotCarved)
        carveOwner st))
  -- An exhausted untyped: three pages, then nothing.
  let carveN : SystemState → Nat → Except KernelError (Unit × SystemState) :=
    fun s n => dispatchSyscall (decodeCarve slotUtRetype frameTag n slotOwnCnRW (n - 950))
      carveOwner s
  match carveN st 960 with
  | .error _ => assertBool "the first of three carves succeeds" false
  | .ok ((), a) => match carveN a 961 with
    | .error _ => assertBool "the second of three carves succeeds" false
    | .ok ((), b) => match carveN b 962 with
      | .error _ => assertBool "the third of three carves succeeds" false
      | .ok ((), c) =>
        assertBool "a fourth carve of a three-page untyped is refused (untypedRegionExhausted)"
          (isErr .untypedRegionExhausted (carveN c 963))
  assertBool "the carve refusals are refusals (no success path leaks through)"
    (refused (dispatchSyscall (decodeCarve slotUtNoRetype frameTag 953 slotOwnCnRW slotCarved)
      carveOwner st))

-- ============================================================================
-- §5e  WS-BP BP7.1 (`v0.36.6`) — memory returns to its untyped
-- ============================================================================

/-- `.untypedReset`, invoked on the capability at `utSlot`; no message registers. -/
private def decodeReset (utSlot : Nat) : SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat utSlot
  , msgInfo   := { length := 0, extraCaps := 0, label := 0 }
  , syscallId := .untypedReset
  , msgRegs   := #[] }

/-- `.cspaceRevoke` of `slot` in the owner's CSpace root, invoked on the
writable root capability. -/
private def decodeRevoke (slot : Nat) : SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat slotOwnCnRW
  , msgInfo   := { length := 1, extraCaps := 0, label := 0 }
  , syscallId := .cspaceRevoke
  , msgRegs   := #[SeLe4n.RegValue.ofNat slot] }

/-- `.cspaceCopy` of `src` to `dst` in the owner's CSpace root, invoked on the
grant-bearing root capability. -/
private def decodeCopy (src dst : Nat) : SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat slotOwnCnGrant
  , msgInfo   := { length := 2, extraCaps := 0, label := 0 }
  , syscallId := .cspaceCopy
  , msgRegs   := #[SeLe4n.RegValue.ofNat src, SeLe4n.RegValue.ofNat dst] }

/-- Run a list of dispatches in order, stopping at the first refusal. -/
private def runAll (st : SystemState) :
    List SyscallDecodeResult → Except KernelError SystemState
  | [] => .ok st
  | d :: ds => match dispatchSyscall d carveOwner st with
    | .error e => .error e
    | .ok ((), st') => runAll st' ds

private def runResetChecks : IO Unit := do
  IO.println "-- §5e `.untypedReset` hands an untyped's memory back (WS-BP BP7.1)"
  let isErr (e : KernelError) (r : Except KernelError (Unit × SystemState)) : Bool :=
    match r with | .error e' => e' == e | .ok _ => false
  -- Carve two frames, map the first, and map a DEVICE frame from the other
  -- untyped: the reset must remove the first mapping and keep the device one.
  match runAll carveScenario
      [decodeCarve slotUtRetype frameTag 950 slotOwnCnRW slotCarved,
       decodeCarve slotUtRetype frameTag 951 slotOwnCnRW 9,
       decodeOwnMap 0x60000 slotCarved permsRWUC,
       decodeCarve slotDevUt frameTag 952 slotOwnCnRW 11,
       decodeOwnMap 0x70000 11 11] with
  | .error e => assertBool s!"the carve-and-map setup succeeds (got {repr e})" false
  | .ok st => do
    assertBool "setup: the carved page is mapped at 0x60000"
      (mappedPaddr st carveAsid (SeLe4n.VAddr.ofNat 0x60000) == some carveUtBase)
    assertBool "setup: the device page is mapped at 0x70000"
      (mappedPaddr st carveAsid (SeLe4n.VAddr.ofNat 0x70000) == some carveDevBase)
    -- While a capability to a carved frame survives, the reset is refused.
    assertBool "a reset while the frame capabilities survive is refused (revocationRequired)"
      (isErr .revocationRequired (dispatchSyscall (decodeReset slotUtRetype) carveOwner st))
    assertBool "a reset without `.retype` over the untyped is refused (illegalAuthority)"
      (isErr .illegalAuthority (dispatchSyscall (decodeReset slotUtNoRetype) carveOwner st))
    assertBool "a `.retype` capability to a non-untyped is refused (untypedTypeMismatch)"
      (isErr .untypedTypeMismatch (dispatchSyscall (decodeReset slotVspRetype) carveOwner st))
    -- THE SIBLING COPY.  Copy the untyped capability to slot 10: the copy is a
    -- CDT child of slot 0 and has no derivations of its own, so a per-slot
    -- "no children" test on it would pass — while the frames carved through
    -- slot 0 are still named by slots 8 and 9.  The reset asks the objects.
    match dispatchSyscall (decodeCopy slotUtRetype 10) carveOwner st with
    | .error e => assertBool s!"copying the untyped capability succeeds (got {repr e})" false
    | .ok ((), stCopy) =>
      assertBool "a reset through a derivation-free SIBLING copy is still refused"
        (isErr .revocationRequired (dispatchSyscall (decodeReset 10) carveOwner stCopy))
    -- An in-flight capability counts: a blocked sender parking a transfer
    -- capability to a carved frame keeps the reset refused even with every
    -- slot cleared.
    match dispatchSyscall (decodeRevoke slotUtRetype) carveOwner st with
    | .error e => assertBool s!"revoking the untyped capability succeeds (got {repr e})" false
    | .ok ((), stRev) => do
      assertBool "revocation removed both frame capabilities"
        (SystemState.lookupSlotCap stRev { cnode := carveCn, slot := SeLe4n.Slot.ofNat slotCarved }
          == none &&
         SystemState.lookupSlotCap stRev { cnode := carveCn, slot := SeLe4n.Slot.ofNat 9 } == none)
      assertBool "but the mapping of the carved page is still there (a mapping records memory)"
        (mappedPaddr stRev carveAsid (SeLe4n.VAddr.ofNat 0x60000) == some carveUtBase)
      let inFlight : TCB :=
        { tid := ⟨990⟩, priority := ⟨10⟩, domain := ⟨0⟩, cspaceRoot := carveCn,
          vspaceRoot := carveVsp, ipcBuffer := SeLe4n.VAddr.ofNat 8192,
          ipcState := .ready,
          pendingMessage := some
            { registers := #[],
              caps := #[TransferCap.fromNode (frameCapability (SeLe4n.ObjId.ofNat 950)) 0] } }
      match storeObject (SeLe4n.ObjId.ofNat 990) (.tcb inFlight) stRev with
      | .error _ => assertBool "the in-flight fixture stores" false
      | .ok ((), stFly) =>
        assertBool "a capability parked in a blocked sender's message keeps the reset refused"
          (isErr .revocationRequired (dispatchSyscall (decodeReset slotUtRetype) carveOwner stFly))
      -- A thread wrote through its mapping before the revocation: the next
      -- owner of the page must not see it.
      let stDirty := { stRev with
        machine := SeLe4n.writeMem stRev.machine (SeLe4n.PAddr.ofNat carveUtBase) 0x5A }
      match dispatchSyscall (decodeReset slotUtRetype) carveOwner stDirty with
      | .error e => assertBool s!"the reset after revocation succeeds (got {repr e})" false
      | .ok ((), stReset) => do
        assertBool "the reset removes the mapping of the region's page"
          (mappedPaddr stReset carveAsid (SeLe4n.VAddr.ofNat 0x60000) == none)
        assertBool "and leaves the mapping of a page OUTSIDE the region alone"
          (mappedPaddr stReset carveAsid (SeLe4n.VAddr.ofNat 0x70000) == some carveDevBase)
        assertBool "the carved frames are retired from the object store"
          ((stReset.objects[SeLe4n.ObjId.ofNat 950]?).isNone &&
           (stReset.objects[SeLe4n.ObjId.ofNat 951]?).isNone)
        assertBool "the device frame, carved from ANOTHER untyped, is untouched"
          (frameAt stReset 952 == some { base := SeLe4n.PAddr.ofNat carveDevBase, isDevice := true })
        assertBool "the untyped's watermark and child list are cleared"
          ((stReset.getUntyped? carveUt).map (fun u => (u.watermark, u.children.length))
            == some (0, 0))
        -- The memory and the id are both reusable, and the page is scrubbed
        -- again before any capability to it exists.
        match dispatchSyscall (decodeCarve slotUtRetype frameTag 950 slotOwnCnRW slotCarved)
            carveOwner stReset with
        | .error e => assertBool s!"a carve after the reset succeeds (got {repr e})" false
        | .ok ((), stAgain) => do
          assertBool "the next carve reuses the region's first page and the retired child id"
            (frameAt stAgain 950 == some { base := SeLe4n.PAddr.ofNat carveUtBase })
          assertBool "and the page is zeroed again — the previous owner's write is gone"
            (SeLe4n.readMem stAgain.machine (SeLe4n.PAddr.ofNat carveUtBase) == 0)
        -- A reset with nothing carved is a no-op success.
        match dispatchSyscall (decodeReset slotUtRetype) carveOwner stReset with
        | .error e => assertBool s!"a second reset of an empty untyped succeeds (got {repr e})" false
        | .ok ((), stTwice) =>
          assertBool "a second reset leaves the untyped empty"
            ((stTwice.getUntyped? carveUt).map (·.watermark) == some 0)
  -- A child that is not a frame cannot be retired: an untyped whose child list
  -- names a kernel object keeps its memory.
  let utWithObjChild : UntypedObject :=
    { regionBase := SeLe4n.PAddr.ofNat carveUtBase, regionSize := 0x3000,
      watermark := SeLe4n.pageBytes,
      children := [{ objId := carveVsp, offset := 0, size := SeLe4n.pageBytes }] }
  match storeObject carveUt (.untyped utWithObjChild) carveScenario with
  | .error _ => assertBool "the non-frame-child fixture stores" false
  | .ok ((), stObj) =>
    assertBool "a reset whose child is not a frame is refused (revocationRequired)"
      (isErr .revocationRequired (dispatchSyscall (decodeReset slotUtRetype) carveOwner stObj))

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
    match dispatchSyscall (decodeMap 7 0x50000 slotFrameRO) attacker st with
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
      (match dispatchSyscall (decodeMap 5 0x50000 slotFrameRO) attacker st with
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
  runAlignmentChecks
  runFrameCapabilityChecks
  runCarveChecks
  runResetChecks
  runAuthorizedChecks
  IO.println "===================================================="
  IO.println "All VSpace capability-binding checks PASS."

end SeLe4n.Testing.VSpaceCapabilityBinding

def main : IO Unit :=
  SeLe4n.Testing.VSpaceCapabilityBinding.runVSpaceCapabilityBindingChecks
