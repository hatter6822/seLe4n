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
import SeLe4n.Platform.Boot

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
* §5f — **WS-BP BP7.1 (`v0.36.7`): a frame capability owns the mapping it
  made.**  `.vspaceMap` records the mapping on the capability; a copy carries
  none; a capability whose mapping is live cannot map again; deleting a frame
  capability removes exactly the mapping it made (seL4's `finaliseCap` →
  `unmapPage`), with the retired non-finalising delete computed beside it; a
  record gone stale removes nothing — a different frame mapped since at the
  same address survives — and does not block a fresh map; a CNode holding a
  recording capability is not retyped in place; and the boot refuses a
  configured record.  §5e's revocation witness inverts in the same cut: the
  revocation now removes the mapping the reset used to be the first to remove.
* §5g — **WS-BP BP7.1 slice 4 (`v0.36.8`): an untyped carves child untypeds,
  and a reset returns the whole subtree.**  `.untypedRetype` at the untyped tag
  carves a child untyped of `2^sizeBits` bytes at the parent's watermark, with
  its parent stamped and its memory left unwritten; the child carves a frame,
  zeroed, which maps.  The in-place retype refuses to destroy the child.  After
  one revocation of the parent capability — which destroys the child's
  capability and the grandchild frame's with it — the parent's reset retires
  the child and the frame together and unmaps the page, where the retired
  frames-only reset (computed beside it) would refuse that state forever.
  Every size the decode refuses is exercised.
* §5h — **`v0.36.9`: a VSpace root is never created in place.**  The in-place
  retype built a root at ASID `0` — the boot VSpace root's — and nothing checked
  the ASID was free, so the ASID table's entry moved to the caller's root while
  the owner's was still stored.  The retired guard is computed beside the live
  one on a state holding an ASID-`0` root; the live `.lifecycleRetype` refuses
  the kind (`KernelObjectType.memoryBacked`), and the same retype into an
  endpoint is the control.
* §5i — **WS-BP BP7.1 slice 4b (`v0.36.10`): an address space is carved
  memory.**  `.untypedRetype` at the VSpace-root tag carves a root on a zeroed
  page of its untyped, under the least free ASID — never `0`, never one another
  root holds — with a read/write capability; a frame maps into it; a device
  untyped cannot back one.  After one revocation the reset retires both roots
  and the frame, removes the carved address space's translation and releases
  both ASIDs, while a thread still running in a carved root refuses the reset;
  the next carve reuses the released ASID and page.
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
#check @SeLe4n.Kernel.untypedRetypeObject
#check @SeLe4n.Kernel.untypedRetypeObject_ok_decompose
#check @SeLe4n.Kernel.untypedRetypeObject_ok_frame
#check @SeLe4n.Kernel.untypedRetypeObject_ok_untyped
#check @SeLe4n.Kernel.untypedNextFrame_of_retype_ok
#check @SeLe4n.Kernel.untypedNextChild_of_retype_ok
#check @SeLe4n.Kernel.untypedRetypeFromCap_ok
#check @SeLe4n.Kernel.carveRequestOf?_ok
#check @SeLe4n.Kernel.untypedRetypeObject_preserves_ipcInvariantFull
#check @SeLe4n.Kernel.untypedCarvedSubtree_spec
#check @SeLe4n.Kernel.untypedReset_ok_subtree_absent
#check @SeLe4n.Kernel.untypedReset_ok_retired_pages_unmapped

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

private def victimVaddr : SeLe4n.VAddr := SeLe4n.Testing.fixtureUserVAddr 0x40000
private def victimPaddr : SeLe4n.PAddr := SeLe4n.PAddr.ofNat 0x90000
private def freshVaddr  : SeLe4n.VAddr := SeLe4n.Testing.fixtureUserVAddr 0x50000

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
      |>.withObject victimVsp (.vspaceRoot (fixtureMappableRoot victimAsid))
      |>.withObject attackerVsp (.vspaceRoot (fixtureMappableRoot attackerAsid (SeLe4n.PAddr.ofNat 0x7E000)))
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
  , msgRegs   := #[SeLe4n.RegValue.ofNat asid, SeLe4n.RegValue.ofNat (SeLe4n.VAddr.userWindowBase + vaddr)] }

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
  , msgRegs   := #[SeLe4n.RegValue.ofNat asid, SeLe4n.RegValue.ofNat (SeLe4n.VAddr.userWindowBase + vaddr),
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

/-- The `.vspaceMap` frame guard as it stood before `v0.36.32`: it refused a
cacheable or executable mapping of a DEVICE frame and admitted an uncached
mapping of a RAM frame.  Spelled here, and nowhere else, so the suite can show
the live guard's new clause is what refuses the uncached RAM alias. -/
private def retiredFrameMappingAdmissible (frameCap : Capability) (frame : FrameObject)
    (perms : PagePermissions) : Except KernelError Unit :=
  if perms.write && !frameCap.hasRight .write then .error .illegalAuthority
  else if frame.isDevice && (perms.execute || perms.cacheable) then .error .policyDenied
  else .ok ()

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
    -- A RAM frame is mapped cacheable or not at all (v0.36.32): an uncached
    -- user alias of RAM the kernel writes through its cacheable identity map
    -- is a mismatched-attribute alias (ARM ARM B2.8), so the carve's zeroes
    -- could reach the thread late and the page's previous owner's bytes early.
    -- The retired guard is computed beside the live one on the same request.
    let rRamU := dispatchSyscall (decodeMap 7 0x50000 slotFrameRO permsRU) attacker st
    assertBool "an UNCACHED mapping of a RAM frame is refused (policyDenied)"
      (isErr .policyDenied rRamU && nothingMapped rRamU)
    match st.getFrame? frameA with
    | none => assertBool "frame A resolves" false
    | some fA =>
      let uncached := PagePermissions.ofNat permsRU
      let admitted (r : Except KernelError Unit) : Bool :=
        match r with | .ok () => true | .error _ => false
      let deniedByPolicy (r : Except KernelError Unit) : Bool :=
        match r with | .error .policyDenied => true | _ => false
      assertBool "...which the RETIRED guard admitted (the decision is the new clause)"
        (admitted (retiredFrameMappingAdmissible (frameCapTo frameA [.read]) fA uncached)
          && deniedByPolicy
               (SeLe4n.Kernel.frameMappingAdmissible (frameCapTo frameA [.read]) fA uncached))
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
      |>.withObject carveVsp (.vspaceRoot (fixtureMappableRoot carveAsid (SeLe4n.PAddr.ofNat 0x7D000)))
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
  , msgRegs   := #[SeLe4n.RegValue.ofNat 6, SeLe4n.RegValue.ofNat (SeLe4n.VAddr.userWindowBase + vaddr),
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
        (mappedPaddr st2 carveAsid (SeLe4n.Testing.fixtureUserVAddr 0x60000) == some carveUtBase)
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
      (dispatchSyscall (decodeCarve slotUtRetype 10 953 slotOwnCnRW slotCarved) carveOwner st))
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
      (mappedPaddr st carveAsid (SeLe4n.Testing.fixtureUserVAddr 0x60000) == some carveUtBase)
    assertBool "setup: the device page is mapped at 0x70000"
      (mappedPaddr st carveAsid (SeLe4n.Testing.fixtureUserVAddr 0x70000) == some carveDevBase)
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
      -- WS-BP BP7.1 (`v0.36.7`): the revocation also REMOVES the mapping the
      -- destroyed frame capability made — seL4's `finaliseCap` → `unmapPage`.
      -- Until then it stayed until the reset, so a thread went on reading and
      -- writing memory whose every capability had been revoked.  The revocation
      -- STEP alone — the retired arm, with no teardown — is computed beside the
      -- live arm on the same state, so the assertion is known to discriminate;
      -- and the step REPORTS the destroyed capability's page, which is exactly
      -- what the teardown then removes.
      assertBool "the revocation removes the mapping the destroyed frame capability recorded"
        (mappedPaddr stRev carveAsid (SeLe4n.Testing.fixtureUserVAddr 0x60000) == none)
      assertBool "RETIRED: the revocation step without its teardown left that mapping in place"
        (match cspaceRevokeCdt { cnode := carveCn, slot := SeLe4n.Slot.ofNat slotUtRetype } st with
          | .ok (_, stOld) =>
              mappedPaddr stOld carveAsid (SeLe4n.Testing.fixtureUserVAddr 0x60000) == some carveUtBase
          | .error _ => false)
      assertBool "the revocation step reports exactly the page the destroyed capability recorded"
        (match cspaceRevokeCdt { cnode := carveCn, slot := SeLe4n.Slot.ofNat slotUtRetype } st with
          | .ok (pages, _) =>
              pages.map (fun p => (p.asid, p.vaddr.toNat, p.paddr.toNat))
                == [(carveAsid, (SeLe4n.Testing.fixtureUserVAddr 0x60000).toNat, carveUtBase)]
          | .error _ => false)
      assertBool "and it leaves the mapping of a page no destroyed capability recorded alone"
        (mappedPaddr stRev carveAsid (SeLe4n.Testing.fixtureUserVAddr 0x70000) == some carveDevBase)
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
        assertBool "after the reset the region's page is mapped nowhere"
          (mappedPaddr stReset carveAsid (SeLe4n.Testing.fixtureUserVAddr 0x60000) == none)
        assertBool "and leaves the mapping of a page OUTSIDE the region alone"
          (mappedPaddr stReset carveAsid (SeLe4n.Testing.fixtureUserVAddr 0x70000) == some carveDevBase)
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
    assertBool "a reset whose child is neither a frame nor an untyped is refused (revocationRequired)"
      (isErr .revocationRequired (dispatchSyscall (decodeReset slotUtRetype) carveOwner stObj))

-- ============================================================================
-- §5g  WS-BP BP7.1 slice 4 (`v0.36.8`) — child untypeds, and subtree resets
-- ============================================================================

/-- The untyped tag with a size in MR0's upper bits. -/
private def untypedTagOfSize (sizeBits : Nat) : Nat := 5 + sizeBits * 256

/-- The RETIRED reset guard (`v0.36.6`–`v0.36.7`): every **direct** child must be
a frame.  Spelled here and nowhere else, so the witness below can show the state
it would refuse forever. -/
private def retiredFramesOnlyRetirable (st : SystemState) (ut : UntypedObject) : Bool :=
  ut.children.all fun c => (st.getFrame? c.objId).isSome

/-- `.lifecycleRetype` of `target` into an endpoint, invoked on the capability at
`capSlot`. -/
private def decodeInPlaceRetype (capSlot target : Nat) : SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat capSlot
  , msgInfo   := { length := 3, extraCaps := 0, label := 0 }
  , syscallId := .lifecycleRetype
  , msgRegs   := #[SeLe4n.RegValue.ofNat target, SeLe4n.RegValue.ofNat 1,
                   SeLe4n.RegValue.ofNat 64] }

private def runChildUntypedChecks : IO Unit := do
  IO.println "-- §5g `.untypedRetype` carves child untypeds, and a reset returns the subtree (WS-BP BP7.1)"
  let st := carveScenario
  let isErr (e : KernelError) (r : Except KernelError (Unit × SystemState)) : Bool :=
    match r with | .error e' => e' == e | .ok _ => false
  -- The sizes the decode refuses, before anything is resolved.
  assertBool "a child untyped smaller than a page is refused (invalidArgument)"
    (isErr .invalidArgument (dispatchSyscall
      (decodeCarve slotUtRetype (untypedTagOfSize 11) 970 slotOwnCnRW 12) carveOwner st))
  assertBool "a child untyped above seL4_MaxUntypedBits is refused (invalidArgument)"
    (isErr .invalidArgument (dispatchSyscall
      (decodeCarve slotUtRetype (untypedTagOfSize 48) 970 slotOwnCnRW 12) carveOwner st))
  assertBool "a frame with a non-zero size is refused (invalidArgument) — a frame is one page"
    (isErr .invalidArgument (dispatchSyscall
      (decodeCarve slotUtRetype (frameTag + 12 * 256) 970 slotOwnCnRW 12) carveOwner st))
  assertBool "a child larger than the parent's free region is refused (untypedRegionExhausted)"
    (isErr .untypedRegionExhausted (dispatchSyscall
      (decodeCarve slotUtRetype (untypedTagOfSize 14) 970 slotOwnCnRW 12) carveOwner st))
  -- Carve a one-page child untyped into slot 12, a frame out of it into slot 13,
  -- and map the frame.
  match dispatchSyscall (decodeCarve slotUtRetype (untypedTagOfSize 12) 970 slotOwnCnRW 12)
      carveOwner st with
  | .error e => assertBool s!"the child-untyped carve succeeds (got {repr e})" false
  | .ok ((), st1) => do
    assertBool "the child untyped is the parent's first page, parent stamped, nothing carved"
      ((st1.getUntyped? (SeLe4n.ObjId.ofNat 970)).map
          (fun u => (u.regionBase.toNat, u.regionSize, u.parent, u.watermark,
                     u.children.length, u.isDevice))
        == some (carveUtBase, SeLe4n.pageBytes, some carveUt, 0, 0, false))
    assertBool "the parent's watermark advances by the child's size"
      (watermarkOf st1 carveUt == some SeLe4n.pageBytes)
    assertBool "carving an untyped writes none of its memory (the frame carve zeroes a page)"
      (SeLe4n.readMem st1.machine (SeLe4n.PAddr.ofNat carveUtBase) == 0xAB)
    assertBool "the destination holds a read/write/retype capability to the child"
      (SystemState.lookupSlotCap st1 { cnode := carveCn, slot := SeLe4n.Slot.ofNat 12 }
        == some (untypedCapability (SeLe4n.ObjId.ofNat 970)))
    assertBool "the in-place retype refuses to destroy the carved untyped (revocationRequired)"
      (isErr .revocationRequired (dispatchSyscall (decodeInPlaceRetype 12 970) carveOwner st1))
    match runAll st1
        [decodeCarve 12 frameTag 971 slotOwnCnRW 13,
         decodeOwnMap 0x60000 13 permsRWUC] with
    | .error e => assertBool s!"carving a frame from the child and mapping it succeeds (got {repr e})" false
    | .ok st2 => do
      assertBool "the grandchild frame is the child's first page"
        (frameAt st2 971 == some { base := SeLe4n.PAddr.ofNat carveUtBase })
      assertBool "and the frame carve zeroed it"
        (SeLe4n.readMem st2.machine (SeLe4n.PAddr.ofNat carveUtBase) == 0)
      assertBool "and it maps"
        (mappedPaddr st2 carveAsid (SeLe4n.Testing.fixtureUserVAddr 0x60000) == some carveUtBase)
      assertBool "the child is exhausted after one page (untypedRegionExhausted)"
        (isErr .untypedRegionExhausted
          (dispatchSyscall (decodeCarve 12 frameTag 972 slotOwnCnRW 14) carveOwner st2))
      assertBool "a reset of the parent while the child's capability lives is refused"
        (isErr .revocationRequired (dispatchSyscall (decodeReset slotUtRetype) carveOwner st2))
      -- One revocation of the parent capability reaches the child's capability
      -- AND the grandchild frame's, which was derived from it.
      match dispatchSyscall (decodeRevoke slotUtRetype) carveOwner st2 with
      | .error e => assertBool s!"revoking the parent capability succeeds (got {repr e})" false
      | .ok ((), stRev) => do
        assertBool "the revocation removed the child's and the grandchild frame's capabilities"
          (SystemState.lookupSlotCap stRev { cnode := carveCn, slot := SeLe4n.Slot.ofNat 12 }
            == none &&
           SystemState.lookupSlotCap stRev { cnode := carveCn, slot := SeLe4n.Slot.ofNat 13 }
            == none)
        -- THE RETIRED GUARD.  The parent's only child is an untyped, so the
        -- frames-only reset refuses — and no capability to the child remains, so
        -- nothing can ever reset the child first: the parent's memory would be
        -- stranded for good.
        assertBool "RETIRED: the frames-only reset guard refuses this state"
          (match stRev.getUntyped? carveUt with
            | some ut => !retiredFramesOnlyRetirable stRev ut
            | none => false)
        match dispatchSyscall (decodeReset slotUtRetype) carveOwner stRev with
        | .error e => assertBool s!"the parent's reset retires the subtree (got {repr e})" false
        | .ok ((), stReset) => do
          assertBool "the child untyped and the grandchild frame are both retired"
            ((stReset.objects[SeLe4n.ObjId.ofNat 970]?).isNone &&
             (stReset.objects[SeLe4n.ObjId.ofNat 971]?).isNone)
          assertBool "and the grandchild's page is mapped nowhere"
            (mappedPaddr stReset carveAsid (SeLe4n.Testing.fixtureUserVAddr 0x60000) == none)
          assertBool "and the parent is empty again"
            ((stReset.getUntyped? carveUt).map (fun u => (u.watermark, u.children.length))
              == some (0, 0))
          -- Both ids and the memory are reusable: carve a larger child in the same place.
          match dispatchSyscall
              (decodeCarve slotUtRetype (untypedTagOfSize 13) 971 slotOwnCnRW 12)
              carveOwner stReset with
          | .error e => assertBool s!"a carve after the subtree reset succeeds (got {repr e})" false
          | .ok ((), stAgain) =>
            assertBool "the next child reuses the region's start and a retired id"
              ((stAgain.getUntyped? (SeLe4n.ObjId.ofNat 971)).map
                  (fun u => (u.regionBase.toNat, u.regionSize))
                == some (carveUtBase, 2 * SeLe4n.pageBytes))
  -- A device untyped yields a device child, and that child a device frame.
  match runAll st
      [decodeCarve slotDevUt (untypedTagOfSize 12) 975 slotOwnCnRW 12,
       decodeCarve 12 frameTag 976 slotOwnCnRW 13] with
  | .error e => assertBool s!"a device child and its frame carve (got {repr e})" false
  | .ok stD => do
    assertBool "a device untyped's child untyped is a device untyped"
      ((stD.getUntyped? (SeLe4n.ObjId.ofNat 975)).map (·.isDevice) == some true)
    assertBool "and its frame is a device frame, left unscrubbed"
      (frameAt stD 976 == some { base := SeLe4n.PAddr.ofNat carveDevBase, isDevice := true } &&
       SeLe4n.readMem stD.machine (SeLe4n.PAddr.ofNat carveDevBase) == 0xCD)

-- ============================================================================
-- §5f  WS-BP BP7.1 (`v0.36.7`) — a frame capability owns the mapping it made
-- ============================================================================

/-- `.cspaceDelete` of `slot` in the owner's CSpace root, invoked on the
writable root capability. -/
private def decodeDelete (slot : Nat) : SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat slotOwnCnRW
  , msgInfo   := { length := 1, extraCaps := 0, label := 0 }
  , syscallId := .cspaceDelete
  , msgRegs   := #[SeLe4n.RegValue.ofNat slot] }

/-- `.vspaceUnmap` of `vaddr` in the owner's address space, invoked on the
owner's VSpace-root capability — the unmap that leaves a record stale. -/
private def decodeOwnUnmap (vaddr : Nat) : SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat slotOwnVsp
  , msgInfo   := { length := 2, extraCaps := 0, label := 0 }
  , syscallId := .vspaceUnmap
  , msgRegs   := #[SeLe4n.RegValue.ofNat 6, SeLe4n.RegValue.ofNat (SeLe4n.VAddr.userWindowBase + vaddr)] }

/-- The mapping record on the capability in the owner's root at `slot`. -/
private def recordAt (st : SystemState) (slot : Nat) : Option FrameMapping :=
  (SystemState.lookupSlotCap st { cnode := carveCn, slot := SeLe4n.Slot.ofNat slot }).bind
    (·.mapping)

-- ============================================================================
-- §5h  `v0.36.9` — a VSpace root is never created in place
-- ============================================================================

/-- A root at ASID `0`, the ASID the boot VSpace root holds, stored at `950`. -/
private def asidZeroRootId : SeLe4n.ObjId := ⟨950⟩

/-- §5g's scenario with an ASID-`0` root registered in the ASID table, as the
boot's own root is, and the lifecycle metadata the retype's first check reads
recorded for the target root (the builder records none), so a refusal below is
the kind's and not a metadata mismatch. -/
private def asidZeroScenario : SystemState :=
  let base := { carveScenario with
    lifecycle := { carveScenario.lifecycle with
      objectTypes := carveScenario.lifecycle.objectTypes.insert carveVsp .vspaceRoot } }
  match storeObject asidZeroRootId
      (.vspaceRoot { asid := SeLe4n.ASID.ofNat 0, mappings := {} }) base with
  | .ok ((), st) => st
  | .error _ => base

/-- `.lifecycleRetype` of `target` into the kind at `tag`, invoked on the
capability at `capSlot`. -/
private def decodeInPlaceRetypeTo (capSlot target tag : Nat) : SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat capSlot
  , msgInfo   := { length := 3, extraCaps := 0, label := 0 }
  , syscallId := .lifecycleRetype
  , msgRegs   := #[SeLe4n.RegValue.ofNat target, SeLe4n.RegValue.ofNat tag,
                   SeLe4n.RegValue.ofNat 64] }

/-- The RETIRED admissibility guard (`v0.36.4`–`v0.36.8`): well-formed, the
slot's identity, and not an untyped or a frame — a VSpace root passed it.
Spelled here and nowhere else, so the witness can show what it admitted. -/
private def retiredAdmissible (newObj : KernelObject) (target : SeLe4n.ObjId)
    (st : SystemState) : Bool :=
  decide (newObj.wellFormed st.objects) && newObj.embeddedIdentityMatches target &&
    !(newObj.objectType == .untyped || newObj.objectType == .frame)

private def runInPlaceVSpaceRootChecks : IO Unit := do
  IO.println "-- §5h a VSpace root is never created in place (v0.36.9)"
  let st := asidZeroScenario
  let zero := SeLe4n.ASID.ofNat 0
  assertBool "setup: ASID 0 is registered to the ASID-0 root"
    (st.asidTable[zero]? == some asidZeroRootId)
  let replacement := objectOfKernelType .vspaceRoot 64
  assertBool "the replacement a retype to a VSpace root builds carries ASID 0"
    (match replacement with | .vspaceRoot r => r.asid == zero | _ => false)
  -- The retired guard admitted it, and the store it guarded took ASID 0.
  assertBool "RETIRED: the pre-v0.36.9 guard admits the replacement"
    (retiredAdmissible replacement carveVsp st)
  match storeObject carveVsp replacement st with
  | .error _ => assertBool "RETIRED: the store succeeds" false
  | .ok ((), stBad) =>
    assertBool "RETIRED: ASID 0 now resolves to the caller's root, and the ASID-0 root is still stored"
      (stBad.asidTable[zero]? == some carveVsp &&
        (stBad.getVSpaceRoot? asidZeroRootId).isSome)
  -- The live arm refuses it, and changes nothing.
  assertBool "the live guard refuses a VSpace-root replacement"
    (!decide (retypeReplacementAdmissible replacement carveVsp st.objects))
  match dispatchSyscall (decodeInPlaceRetypeTo slotVspRetype carveVsp.toNat 4) carveOwner st with
  | .ok _ => assertBool "the live `.lifecycleRetype` into a VSpace root is refused" false
  | .error e =>
    assertBool "the live `.lifecycleRetype` into a VSpace root is refused (illegalState)"
      (e == .illegalState)
  -- CONTROL: the same capability, the same target, another kind succeeds, so the
  -- refusal is about the kind and not the authority.
  match dispatchSyscall (decodeInPlaceRetypeTo slotVspRetype carveVsp.toNat 1) carveOwner st with
  | .error e => assertBool s!"CONTROL: the same retype into an endpoint succeeds (got {repr e})" false
  | .ok ((), stOk) =>
    assertBool "CONTROL: the same retype into an endpoint succeeds, and ASID 0 stays the ASID-0 root's"
      ((stOk.getEndpoint? carveVsp).isSome && stOk.asidTable[zero]? == some asidZeroRootId)

-- ============================================================================
-- §5i  WS-BP BP7.1 slice 4b (`v0.36.10`) — an address space is carved memory
-- ============================================================================

/-- The VSpace-root tag. -/
private def vspaceRootTag : Nat := 4

/-- `.vspaceMap` through the root capability at `rootSlot`, under `asid`. -/
private def decodeMapVia (rootSlot asid vaddr frameSlot perms : Nat) : SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat rootSlot
  , msgInfo   := { length := 4, extraCaps := 0, label := 0 }
  , syscallId := .vspaceMap
  , msgRegs   := #[SeLe4n.RegValue.ofNat asid, SeLe4n.RegValue.ofNat (SeLe4n.VAddr.userWindowBase + vaddr),
                   SeLe4n.RegValue.ofNat frameSlot, SeLe4n.RegValue.ofNat perms] }

/-- The root stored at `oid`, if one is. -/
private def rootAt (st : SystemState) (oid : Nat) : Option VSpaceRoot :=
  st.getVSpaceRoot? (SeLe4n.ObjId.ofNat oid)

private def runCarvedRootChecks : IO Unit := do
  IO.println "-- §5i `.untypedRetype` carves a VSpace root, and the reset retires it (WS-BP BP7.1)"
  let st := carveScenario
  let isErr (e : KernelError) (r : Except KernelError (Unit × SystemState)) : Bool :=
    match r with | .error e' => e' == e | .ok _ => false
  let one := SeLe4n.ASID.ofNat 1
  assertBool "a VSpace root with a non-zero size is refused (invalidArgument) — a root is one page"
    (isErr .invalidArgument (dispatchSyscall
      (decodeCarve slotUtRetype (vspaceRootTag + 256) 980 slotOwnCnRW 12) carveOwner st))
  assertBool "a device untyped cannot back a VSpace root (untypedDeviceRestriction) — a table is RAM"
    (isErr .untypedDeviceRestriction (dispatchSyscall
      (decodeCarve slotDevUt vspaceRootTag 980 slotOwnCnRW 12) carveOwner st))
  match runAll st
      [decodeCarve slotUtRetype vspaceRootTag 980 slotOwnCnRW 12,
       decodeCarve slotUtRetype vspaceRootTag 981 slotOwnCnRW 13,
       decodeCarve slotUtRetype frameTag 982 slotOwnCnRW 14] with
  | .error e => assertBool s!"carving two roots and a frame succeeds (got {repr e})" false
  | .ok st1 => do
    assertBool "the first root is registered under the least free ASID (1), not 0"
      ((rootAt st1 980).map (·.asid) == some one && st1.asidTable[one]? == some (SeLe4n.ObjId.ofNat 980))
    assertBool "the second root takes the next free ASID (2)"
      ((rootAt st1 981).map (·.asid) == some (SeLe4n.ASID.ofNat 2))
    assertBool "the boot-configured root keeps its own ASID"
      (st1.asidTable[carveAsid]? == some carveVsp)
    assertBool "the first root's table base is the untyped's first page"
      ((rootAt st1 980).bind (·.tableBase) == some (SeLe4n.PAddr.ofNat carveUtBase))
    assertBool "and the carve zeroed that page (it held 0xAB)"
      (SeLe4n.readMem st1.machine (SeLe4n.PAddr.ofNat carveUtBase) == 0)
    assertBool "the destination holds a read/write capability to the root"
      (SystemState.lookupSlotCap st1 { cnode := carveCn, slot := SeLe4n.Slot.ofNat 12 }
        == some (vspaceRootCapability (SeLe4n.ObjId.ofNat 980)))
    -- `v0.36.12`: a carved address space holds no table below its root until
    -- one is installed (§5k), so the frame has no walk to hang from.
    assertBool "the frame is refused in a carved address space with no tables (translationFault)"
      (isErr .translationFault (dispatchSyscall (decodeMapVia 12 1 0x70000 14 permsRWUC)
        carveOwner st1))
    assertBool "a reset while the roots' capabilities live is refused (revocationRequired)"
      (isErr .revocationRequired (dispatchSyscall (decodeReset slotUtRetype) carveOwner st1))
    match dispatchSyscall (decodeRevoke slotUtRetype) carveOwner st1 with
    | .error e => assertBool s!"revoking the untyped capability succeeds (got {repr e})" false
    | .ok ((), stRev) => do
      -- A thread still running in a carved root names it without a capability.
      let stUsed : SystemState :=
        match stRev.getTcb? carveOwner with
        | some t =>
          match storeObject carveOwner.toObjId
              (.tcb { t with vspaceRoot := SeLe4n.ObjId.ofNat 980 }) stRev with
          | .ok ((), s) => s
          | .error _ => stRev
        | none => stRev
      assertBool "a reset while a thread's vspaceRoot names a carved root is refused (revocationRequired)"
        (isErr .revocationRequired (dispatchSyscall (decodeReset slotUtRetype) carveOwner stUsed))
      match dispatchSyscall (decodeReset slotUtRetype) carveOwner stRev with
      | .error e => assertBool s!"CONTROL: with no thread in it, the reset retires the roots (got {repr e})" false
      | .ok ((), stReset) => do
        assertBool "CONTROL: both roots and the frame are retired"
          ((stReset.objects[SeLe4n.ObjId.ofNat 980]?).isNone &&
           (stReset.objects[SeLe4n.ObjId.ofNat 981]?).isNone &&
           (stReset.objects[SeLe4n.ObjId.ofNat 982]?).isNone)
        assertBool "their ASIDs are released, and the boot root's is untouched"
          (stReset.asidTable[one]? == none && stReset.asidTable[SeLe4n.ASID.ofNat 2]? == none &&
           stReset.asidTable[carveAsid]? == some carveVsp)
        match dispatchSyscall (decodeCarve slotUtRetype vspaceRootTag 980 slotOwnCnRW 12)
            carveOwner stReset with
        | .error e => assertBool s!"a root carve after the reset succeeds (got {repr e})" false
        | .ok ((), stAgain) =>
          assertBool "the next root reuses the released ASID and the region's first page"
            ((rootAt stAgain 980).map (fun r => (r.asid, r.tableBase))
              == some (one, some (SeLe4n.PAddr.ofNat carveUtBase)))

private def runFrameFinaliseChecks : IO Unit := do
  IO.println "-- §5f a frame capability owns the mapping it made (WS-BP BP7.1)"
  let isErr (e : KernelError) (r : Except KernelError (Unit × SystemState)) : Bool :=
    match r with | .error e' => e' == e | .ok _ => false
  -- Carve two frames (slots 8, 9), map the first through slot 8 at 0x60000,
  -- and copy slot 8 to slot 12.
  match runAll carveScenario
      [decodeCarve slotUtRetype frameTag 950 slotOwnCnRW slotCarved,
       decodeCarve slotUtRetype frameTag 951 slotOwnCnRW 9,
       decodeOwnMap 0x60000 slotCarved permsRWUC,
       decodeCopy slotCarved 12] with
  | .error e => assertBool s!"the carve-map-copy setup succeeds (got {repr e})" false
  | .ok st => do
    assertBool "the map records the mapping on the capability that made it"
      (recordAt st slotCarved == some { asid := carveAsid, vaddr := SeLe4n.Testing.fixtureUserVAddr 0x60000 })
    assertBool "a copy carries no mapping record (seL4's `deriveCap`)"
      (recordAt st 12 == none &&
       (SystemState.lookupSlotCap st { cnode := carveCn, slot := SeLe4n.Slot.ofNat 12 }).isSome)
    assertBool "a capability whose mapping is live cannot map again (invalidCapability)"
      (isErr .invalidCapability
        (dispatchSyscall (decodeOwnMap 0x61000 slotCarved permsRWUC) carveOwner st))
    -- The copy maps the same frame a second time, and deleting the COPY removes
    -- exactly the mapping the copy made.
    match dispatchSyscall (decodeOwnMap 0x61000 12 permsRWUC) carveOwner st with
    | .error e => assertBool s!"the copy maps the frame again (got {repr e})" false
    | .ok ((), st2) => do
      assertBool "setup: the frame is mapped twice"
        (mappedPaddr st2 carveAsid (SeLe4n.Testing.fixtureUserVAddr 0x60000) == some carveUtBase &&
         mappedPaddr st2 carveAsid (SeLe4n.Testing.fixtureUserVAddr 0x61000) == some carveUtBase)
      match dispatchSyscall (decodeDelete 12) carveOwner st2 with
      | .error e => assertBool s!"deleting the copy succeeds (got {repr e})" false
      | .ok ((), st3) => do
        assertBool "deleting a frame capability removes the mapping it made"
          (mappedPaddr st3 carveAsid (SeLe4n.Testing.fixtureUserVAddr 0x61000) == none)
        assertBool "and leaves the mapping another capability made alone"
          (mappedPaddr st3 carveAsid (SeLe4n.Testing.fixtureUserVAddr 0x60000) == some carveUtBase)
        assertBool "RETIRED: the non-finalising delete left the deleted capability's mapping in place"
          (match cspaceDeleteSlot { cnode := carveCn, slot := SeLe4n.Slot.ofNat 12 } st2 with
            | .ok ((), stOld) =>
                mappedPaddr stOld carveAsid (SeLe4n.Testing.fixtureUserVAddr 0x61000) == some carveUtBase
            | .error _ => false)
  -- A STALE record: the address space unmaps 0x60000 through its own VSpace
  -- capability and maps the OTHER frame there.  Deleting slot 8 — whose record
  -- still names 0x60000 — must not remove a mapping it did not make.  (A fresh
  -- chain, with no copy of slot 8: a deleted copy's CDT node keeps its parent
  -- a derivation parent until a revocation, as it always has.)
  match runAll carveScenario
      [decodeCarve slotUtRetype frameTag 950 slotOwnCnRW slotCarved,
       decodeCarve slotUtRetype frameTag 951 slotOwnCnRW 9,
       decodeOwnMap 0x60000 slotCarved permsRWUC,
       decodeOwnUnmap 0x60000,
       decodeOwnMap 0x60000 9 permsRWUC] with
  | .error e => assertBool s!"the map-unmap-remap setup succeeds (got {repr e})" false
  | .ok st4 => do
    assertBool "setup: 0x60000 now maps the second frame, and slot 8's record is stale"
      (mappedPaddr st4 carveAsid (SeLe4n.Testing.fixtureUserVAddr 0x60000)
          == some (carveUtBase + SeLe4n.pageBytes) &&
       recordAt st4 slotCarved == some { asid := carveAsid, vaddr := SeLe4n.Testing.fixtureUserVAddr 0x60000 })
    match dispatchSyscall (decodeDelete slotCarved) carveOwner st4 with
    | .error e => assertBool s!"deleting the stale-record capability succeeds (got {repr e})" false
    | .ok ((), st5) =>
      assertBool "a stale record removes nothing: the other frame's mapping survives"
        (mappedPaddr st5 carveAsid (SeLe4n.Testing.fixtureUserVAddr 0x60000)
          == some (carveUtBase + SeLe4n.pageBytes))
    -- A stale record does not block a fresh map of its capability.
    match dispatchSyscall (decodeOwnMap 0x62000 slotCarved permsRWUC) carveOwner st4 with
    | .error e => assertBool s!"a capability with a stale record maps again (got {repr e})" false
    | .ok ((), st6) =>
      assertBool "and the new mapping replaces the stale record"
        (recordAt st6 slotCarved
          == some { asid := carveAsid, vaddr := SeLe4n.Testing.fixtureUserVAddr 0x62000 })
  -- A CNode whose ONLY obstacle to an in-place retype is a mapping record: a
  -- fresh CNode holding one frame capability with no CDT node at all, so no
  -- derivation-parent guard can be what refuses it.  The control is the same
  -- CNode with the record stripped.
  let recCap : Capability :=
    { frameCapability (SeLe4n.ObjId.ofNat 950) with
      mapping := some { asid := carveAsid, vaddr := SeLe4n.Testing.fixtureUserVAddr 0x60000 } }
  let lone (cap : Capability) : CNode :=
    { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
      slots := SeLe4n.UniqueSlotMap.ofListWF [(SeLe4n.Slot.ofNat 0, cap)] }
  let retypeLone (cap : Capability) : Bool :=
    match storeObject (SeLe4n.ObjId.ofNat 970) (.cnode (lone cap)) carveScenario with
    | .error _ => false
    | .ok ((), stL) =>
      match lifecyclePreRetypeCleanup stL (SeLe4n.ObjId.ofNat 970) (.cnode (lone cap))
          (.endpoint {}) with
      | .error .revocationRequired => false
      | .error _ => false
      | .ok _ => true
  assertBool "a CNode holding a capability that records a mapping is not retyped in place"
    (!retypeLone recCap)
  assertBool "CONTROL: the same CNode with the record stripped is retyped"
    (retypeLone recCap.withoutMapping)
  -- The boot admits no configured record: every mapping is one a capability made.
  assertBool "the boot refuses a configured capability that records a mapping"
    (!SeLe4n.Platform.Boot.bootSafeCapCheck
      { frameCapability (SeLe4n.ObjId.ofNat 950) with
        mapping := some { asid := carveAsid, vaddr := SeLe4n.Testing.fixtureUserVAddr 0x60000 } })
  assertBool "CONTROL: and admits the same capability with no record"
    (SeLe4n.Platform.Boot.bootSafeCapCheck (frameCapability (SeLe4n.ObjId.ofNat 950)))

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

-- ============================================================================
-- §5j  WS-BP BP7.1 (`v0.36.11`) — a thread runs in a carved address space
-- ============================================================================

private def spaceWorker : SeLe4n.ThreadId := ⟨945⟩
private def slotWorkerTcb : Nat := 10  -- a writable capability to the suspended worker
private def slotOwnerTcb  : Nat := 11  -- a writable capability to the running owner

/-- §5d's scenario with a **suspended** worker thread and two TCB capabilities
in the owner's CSpace root: one to the worker, one to the owner itself. -/
private def spaceScenario : SystemState :=
  let st := carveScenario
  let worker : TCB :=
    { tid := spaceWorker, priority := ⟨10⟩, domain := ⟨0⟩,
      cspaceRoot := carveCn, vspaceRoot := carveVsp,
      ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready }
  let st1 := match storeObject spaceWorker.toObjId (.tcb worker) st with
    | .ok ((), s) => s
    | .error _ => st
  match st1.getCNode? carveCn with
  | none => st1
  | some cn =>
    let cn' := (cn.insert (SeLe4n.Slot.ofNat slotWorkerTcb)
        (frameCapTo spaceWorker.toObjId [.read, .write])).insert
      (SeLe4n.Slot.ofNat slotOwnerTcb) (frameCapTo carveOwner.toObjId [.read, .write])
    match storeObject carveCn (.cnode cn') st1 with
    | .ok ((), s) => s
    | .error _ => st1

/-- `.tcbSetSpace` on the TCB capability at `tcbSlot`: MR0 the new CSpace root's
capability address, MR1 the new VSpace root's. -/
private def decodeSetSpace (tcbSlot cnSlot vrSlot : Nat) : SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat tcbSlot
  , msgInfo   := { length := 2, extraCaps := 0, label := 0 }
  , syscallId := .tcbSetSpace
  , msgRegs   := #[SeLe4n.RegValue.ofNat cnSlot, SeLe4n.RegValue.ofNat vrSlot] }

/-- The retired reading of "suspended": the stored flag alone.  Spelled here and
nowhere else, so the witness can show the live check discriminates. -/
private def flagOnlySuspended (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? tid with
  | some t => t.threadState == .Inactive
  | none => false

/-- The roots a thread names, if it is stored. -/
private def rootsOf (st : SystemState) (tid : SeLe4n.ThreadId) : Option (SeLe4n.ObjId × SeLe4n.ObjId) :=
  (st.getTcb? tid).map (fun t => (t.cspaceRoot, t.vspaceRoot))

private def runSetSpaceChecks : IO Unit := do
  IO.println "-- §5j `.tcbSetSpace` puts a suspended thread in a carved address space (WS-BP BP7.1)"
  let st := spaceScenario
  let isErr (e : KernelError) (r : Except KernelError (Unit × SystemState)) : Bool :=
    match r with | .error e' => e' == e | .ok _ => false
  let root := SeLe4n.ObjId.ofNat 980
  match dispatchSyscall (decodeCarve slotUtRetype vspaceRootTag 980 slotOwnCnRW 12) carveOwner st with
  | .error e => assertBool s!"carving a root succeeds (got {repr e})" false
  | .ok ((), st1) => do
    -- The refusals, each on the state the success runs on.
    assertBool "a CSpace-root capability without .grant is refused (illegalAuthority)"
      (isErr .illegalAuthority (dispatchSyscall (decodeSetSpace slotWorkerTcb slotOwnCnRW 12) carveOwner st1))
    assertBool "a read-only CSpace-root capability is refused (illegalAuthority)"
      (isErr .illegalAuthority (dispatchSyscall (decodeSetSpace slotWorkerTcb slotOwnCnRO 12) carveOwner st1))
    assertBool "a CNode capability named as the VSpace root is refused (invalidCapability)"
      (isErr .invalidCapability
        (dispatchSyscall (decodeSetSpace slotWorkerTcb slotOwnCnGrant slotOwnCnRW) carveOwner st1))
    assertBool "an untyped capability named as the VSpace root is refused (invalidCapability)"
      (isErr .invalidCapability
        (dispatchSyscall (decodeSetSpace slotWorkerTcb slotOwnCnGrant slotUtRetype) carveOwner st1))
    assertBool "one message register is refused"
      ((dispatchSyscall { decodeSetSpace slotWorkerTcb slotOwnCnGrant 12 with
          msgInfo := { length := 1, extraCaps := 0, label := 0 },
          msgRegs := #[SeLe4n.RegValue.ofNat slotOwnCnGrant] } carveOwner st1).toOption.isNone)
    -- The decisive case: the running owner's stored flag is the default
    -- `.Inactive`, so the retired flag-only reading would admit it.
    assertBool "CONTROL: the running owner's stored flag reads .Inactive (the retired reading admits it)"
      (flagOnlySuspended st1 carveOwner)
    assertBool "a thread the scheduler runs is refused (illegalState), whatever its flag says"
      (isErr .illegalState (dispatchSyscall (decodeSetSpace slotOwnerTcb slotOwnCnGrant 12) carveOwner st1))
    match dispatchSyscall (decodeSetSpace slotWorkerTcb slotOwnCnGrant 12) carveOwner st1 with
    | .error e => assertBool s!"setting the suspended worker's space succeeds (got {repr e})" false
    | .ok ((), st2) => do
      assertBool "the worker now names the carved root and the CSpace root"
        (rootsOf st2 spaceWorker == some (carveCn, root))
      assertBool "and nothing else about it moved"
        ((st2.getTcb? spaceWorker).map (fun t => (t.priority, t.ipcState, t.threadState))
          == (st1.getTcb? spaceWorker).map (fun t => (t.priority, t.ipcState, t.threadState)))
      assertBool "the owner is untouched"
        (rootsOf st2 carveOwner == rootsOf st1 carveOwner)
      match dispatchSyscall (decodeRevoke slotUtRetype) carveOwner st2 with
      | .error e => assertBool s!"revoking the untyped capability succeeds (got {repr e})" false
      | .ok ((), stRev) => do
        assertBool "the reset refuses while the worker runs in the carved root (revocationRequired)"
          (isErr .revocationRequired (dispatchSyscall (decodeReset slotUtRetype) carveOwner stRev))
        match dispatchSyscall (decodeSetSpace slotWorkerTcb slotOwnCnGrant slotOwnVsp) carveOwner stRev with
        | .error e => assertBool s!"moving the worker back to the boot root succeeds (got {repr e})" false
        | .ok ((), stBack) => do
          assertBool "the worker names the boot root again"
            (rootsOf stBack spaceWorker == some (carveCn, carveVsp))
          assertBool "CONTROL: with no thread in it, the reset retires the carved root"
            (match dispatchSyscall (decodeReset slotUtRetype) carveOwner stBack with
             | .ok ((), s) => (s.objects[root]?).isNone
             | .error _ => false)

-- ============================================================================
-- §5k  WS-BP BP7.1 (`v0.36.12`) — intermediate page tables
-- ============================================================================

/-- The page-table tag. -/
private def pageTableTag : Nat := 9

/-- §5d's scenario with a sixteen-page untyped — room for a root, four tables,
a frame and a child untyped — and a 32-slot CSpace root to hold their
capabilities (slots 16..20 would be refused by a 16-slot root's radix). -/
private def tableScenario : SystemState :=
  let st := carveScenario
  let st1 := match st.getUntyped? carveUt with
    | some ut =>
      match storeObject carveUt (.untyped { ut with regionSize := 0x10000 }) st with
      | .ok ((), s) => s
      | .error _ => st
    | none => st
  match st1.getCNode? carveCn with
  | some cn =>
    match storeObject carveCn (.cnode { cn with depth := 5, radixWidth := 5 }) st1 with
    | .ok ((), s) => s
    | .error _ => st1
  | none => st1

/-- `.pageTableMap` on the table capability at `tableSlot`: MR0 the address
space's capability address, MR1 the virtual address. -/
private def decodeTableMap (tableSlot rootSlot vaddr : Nat) : SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat tableSlot
  , msgInfo   := { length := 2, extraCaps := 0, label := 0 }
  , syscallId := .pageTableMap
  , msgRegs   := #[SeLe4n.RegValue.ofNat rootSlot, SeLe4n.RegValue.ofNat (SeLe4n.VAddr.userWindowBase + vaddr)] }

/-- WS-BP BP7.2: `.vspaceMap` through the root at `rootSlot` naming the raw
virtual address `rawVaddr` — no user-window offset, so a scenario can name an
address below the window, or an unaligned one. -/
private def decodeRawMapVia (rootSlot asid rawVaddr frameSlot perms : Nat) : SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat rootSlot
  , msgInfo   := { length := 4, extraCaps := 0, label := 0 }
  , syscallId := .vspaceMap
  , msgRegs   := #[SeLe4n.RegValue.ofNat asid, SeLe4n.RegValue.ofNat rawVaddr,
                   SeLe4n.RegValue.ofNat frameSlot, SeLe4n.RegValue.ofNat perms] }

/-- WS-BP BP7.2: `.pageTableMap` naming the raw virtual address `rawVaddr`. -/
private def decodeRawTableMap (tableSlot rootSlot rawVaddr : Nat) : SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat tableSlot
  , msgInfo   := { length := 2, extraCaps := 0, label := 0 }
  , syscallId := .pageTableMap
  , msgRegs   := #[SeLe4n.RegValue.ofNat rootSlot, SeLe4n.RegValue.ofNat rawVaddr] }

/-- `.pageTableUnmap` on the table capability at `tableSlot`. -/
private def decodeTableUnmap (tableSlot : Nat) : SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat tableSlot
  , msgInfo   := { length := 0, extraCaps := 0, label := 0 }
  , syscallId := .pageTableUnmap
  , msgRegs   := #[] }

/-- `.vspaceUnmap` through the root capability at `rootSlot`, under `asid`. -/
private def decodeUnmapVia (rootSlot asid vaddr : Nat) : SyscallDecodeResult :=
  { capAddr   := SeLe4n.CPtr.ofNat rootSlot
  , msgInfo   := { length := 2, extraCaps := 0, label := 0 }
  , syscallId := .vspaceUnmap
  , msgRegs   := #[SeLe4n.RegValue.ofNat asid, SeLe4n.RegValue.ofNat (SeLe4n.VAddr.userWindowBase + vaddr)] }

/-- Where the table at `oid` records itself installed. -/
private def installOf (st : SystemState) (oid : Nat) : Option PageTableInstall :=
  (st.getPageTable? (SeLe4n.ObjId.ofNat oid)).bind (·.installedIn)

/-- The (level, table) slots a root holds. -/
private def slotsOf (st : SystemState) (oid : Nat) : Option (List (Nat × Nat)) :=
  (rootAt st oid).map (fun r => r.tables.map (fun s => (s.level, s.table.toNat)))

private def runPageTableChecks : IO Unit := do
  IO.println "-- §5k intermediate page tables: `.pageTableMap` / `.pageTableUnmap` (WS-BP BP7.1)"
  let st := tableScenario
  let isErr (e : KernelError) (r : Except KernelError (Unit × SystemState)) : Bool :=
    match r with | .error e' => e' == e | .ok _ => false
  let one := SeLe4n.ASID.ofNat 1
  let va : Nat := 0x70000
  assertBool "a page table with a non-zero size is refused (invalidArgument) — a table is one page"
    (isErr .invalidArgument (dispatchSyscall
      (decodeCarve slotUtRetype (pageTableTag + 256) 983 slotOwnCnRW 15) carveOwner st))
  assertBool "a device untyped cannot back a page table (untypedDeviceRestriction)"
    (isErr .untypedDeviceRestriction (dispatchSyscall
      (decodeCarve slotDevUt pageTableTag 983 slotOwnCnRW 15) carveOwner st))
  assertBool "a page table is never created in place (the in-place retype refuses it)"
    ((dispatchSyscall (decodeInPlaceRetypeTo slotVspRetype 983 pageTableTag) carveOwner st).toOption.isNone)
  match runAll st
      [decodeCarve slotUtRetype vspaceRootTag 980 slotOwnCnRW 12,
       decodeCarve slotUtRetype frameTag 982 slotOwnCnRW 14,
       decodeCarve slotUtRetype pageTableTag 983 slotOwnCnRW 15,
       decodeCarve slotUtRetype pageTableTag 984 slotOwnCnRW 16,
       decodeCarve slotUtRetype pageTableTag 985 slotOwnCnRW 17,
       decodeCarve slotUtRetype pageTableTag 986 slotOwnCnRW 18] with
  | .error e => assertBool s!"carving a root, a frame and four tables succeeds (got {repr e})" false
  | .ok st1 => do
    assertBool "a carved table is installed nowhere, and its page is zeroed"
      (installOf st1 983 == none &&
       ((st1.getPageTable? (SeLe4n.ObjId.ofNat 983)).map (·.base)).any
         (fun b => SeLe4n.readMem st1.machine b == 0))
    assertBool "the table capability is read/write"
      (SystemState.lookupSlotCap st1 { cnode := carveCn, slot := SeLe4n.Slot.ofNat 15 }
        == some (pageTableCapability (SeLe4n.ObjId.ofNat 983)))
    assertBool "a frame is refused where the walk has no tables (translationFault)"
      (isErr .translationFault (dispatchSyscall (decodeMapVia 12 1 va 14 permsRWUC) carveOwner st1))
    -- A root with no table page — the kernel's own boot root is the one such
    -- root a booted kernel holds — has nowhere for a table to hang from.
    assertBool "a table is refused in a root that owns no page (invalidArgument)"
      (match storeObject carveVsp (.vspaceRoot { asid := SeLe4n.ASID.ofNat 3, mappings := {} }) st1 with
       | .ok ((), s) => isErr .invalidArgument (dispatchSyscall (decodeTableMap 15 slotOwnVsp va) carveOwner s)
       | .error _ => false)
    assertBool "...and a frame is refused there too (translationFault): no table, no walk"
      (match storeObject carveVsp (.vspaceRoot { asid := SeLe4n.ASID.ofNat 3, mappings := {} }) st1 with
       | .ok ((), s) => isErr .translationFault (dispatchSyscall (decodeMapVia slotOwnVsp 3 va 14 permsRWUC) carveOwner s)
       | .error _ => false)
    assertBool "an address outside the 48-bit space has no walk (addressOutOfBounds)"
      (isErr .addressOutOfBounds (dispatchSyscall (decodeTableMap 15 12 (2 ^ 48)) carveOwner st1))
    assertBool "a root capability without .write is refused"
      ((dispatchSyscall (decodeTableMap 15 slotOwnCnRO va) carveOwner st1).toOption.isNone)
    match runAll st1 [decodeTableMap 15 12 va, decodeTableMap 16 12 va] with
    | .error e => assertBool s!"installing two tables succeeds (got {repr e})" false
    | .ok st2 => do
      assertBool "they land at levels 1 and 2, shallowest first, and each records its slot"
        (slotsOf st2 980 == some [(1, 983), (2, 984)] &&
         (installOf st2 983).map (fun i => (i.root.toNat, i.level)) == some (980, 1) &&
         (installOf st2 984).map (fun i => (i.root.toNat, i.level)) == some (980, 2))
      assertBool "a table already installed is refused a second install (invalidCapability)"
        (isErr .invalidCapability (dispatchSyscall (decodeTableMap 15 12 va) carveOwner st2))
      assertBool "two levels are not a walk: the frame is still refused (translationFault)"
        (isErr .translationFault (dispatchSyscall (decodeMapVia 12 1 va 14 permsRWUC) carveOwner st2))
      match runAll st2 [decodeTableMap 17 12 va, decodeMapVia 12 1 va 14 permsRWUC] with
      | .error e => assertBool s!"the third table completes the walk and the frame maps (got {repr e})" false
      | .ok st3 => do
        assertBool "the third table is at level 3, and the frame maps"
          (slotsOf st3 980 == some [(1, 983), (2, 984), (3, 985)] &&
           mappedPaddr st3 one (SeLe4n.Testing.fixtureUserVAddr va) == some (carveUtBase + SeLe4n.pageBytes))
        assertBool "a complete walk has no room for a fourth table (mappingConflict)"
          (isErr .mappingConflict (dispatchSyscall (decodeTableMap 18 12 va) carveOwner st3))
        -- WS-BP BP7.2: the user window.  Level-0 entry 0 of every user root
        -- is the kernel's own window, so neither a table nor a frame may go
        -- below `VAddr.userWindowBase`; and a mapping's virtual address is
        -- page-aligned, as its physical address is.
        assertBool "the user window starts at 2^39 and ends at the canonical bound"
          (!(SeLe4n.VAddr.ofNat (SeLe4n.VAddr.userWindowBase - 1)).inUserWindow &&
           (SeLe4n.VAddr.ofNat SeLe4n.VAddr.userWindowBase).inUserWindow &&
           (SeLe4n.VAddr.ofNat (2 ^ 48 - SeLe4n.pageBytes)).inUserWindow &&
           !(SeLe4n.VAddr.ofNat (2 ^ 48)).inUserWindow)
        assertBool "a table below the user window is refused (addressOutOfBounds)"
          (isErr .addressOutOfBounds (dispatchSyscall (decodeRawTableMap 18 12 va) carveOwner st3))
        assertBool "a frame below the user window is refused (addressOutOfBounds)"
          (isErr .addressOutOfBounds
            (dispatchSyscall (decodeRawMapVia 12 1 va 14 permsRWUC) carveOwner st2))
        -- A copy carries no mapping record, so it may map the frame again;
        -- only the address is wrong.
        assertBool "an unaligned virtual address inside a complete walk is refused (alignmentError)"
          (match runAll st3 [decodeCopy 14 22] with
           | .ok sCopy =>
               isErr .alignmentError
                 (dispatchSyscall
                   (decodeRawMapVia 12 1 (SeLe4n.VAddr.userWindowBase + va + SeLe4n.pageBytes + 8) 22
                     permsRWUC) carveOwner sCopy) &&
               -- CONTROL: the same copy at the aligned page beside it maps.
               (dispatchSyscall
                   (decodeRawMapVia 12 1 (SeLe4n.VAddr.userWindowBase + va + SeLe4n.pageBytes) 22
                     permsRWUC) carveOwner sCopy).isOk
           | .error _ => false)
        assertBool "a table a mapping still passes through is not unmapped (revocationRequired)"
          (isErr .revocationRequired (dispatchSyscall (decodeTableUnmap 17) carveOwner st3))
        assertBool "nor one a deeper table is installed beneath (revocationRequired)"
          (isErr .revocationRequired (dispatchSyscall (decodeTableUnmap 15) carveOwner st3))
        assertBool "a reset while the capabilities live is refused (revocationRequired)"
          (isErr .revocationRequired (dispatchSyscall (decodeReset slotUtRetype) carveOwner st3))
        -- Finalisation (`finaliseDestroyedCapabilities`): destroying a page
        -- table's LAST capability takes it out of its address space, with every
        -- mapping and every table beneath it; destroying one of several leaves
        -- it installed.
        let at15 : CSpaceAddr := { cnode := carveCn, slot := SeLe4n.Slot.ofNat 15 }
        match runAll st3 [decodeCopy 15 21, decodeDelete 21] with
        | .error e => assertBool s!"copying the level-1 table capability, then deleting the copy, succeeds (got {repr e})" false
        | .ok sCopy =>
          assertBool "a table another capability still names stays installed, with everything beneath it"
            (slotsOf sCopy 980 == slotsOf st3 980 &&
             mappedPaddr sCopy one (SeLe4n.Testing.fixtureUserVAddr va) == some (carveUtBase + SeLe4n.pageBytes))
        match dispatchSyscall (decodeDelete 15) carveOwner st3 with
        | .error e => assertBool s!"deleting the level-1 table's only capability succeeds (got {repr e})" false
        | .ok ((), sDel) => do
          assertBool "deleting a table's last capability takes it, and the two tables beneath it, out of the root"
            (slotsOf sDel 980 == some [] &&
             [983, 984, 985].all (fun n => !Architecture.pageTableInstallLive sDel (SeLe4n.ObjId.ofNat n)))
          assertBool "...and the mapping whose walk passed through it"
            (mappedPaddr sDel one (SeLe4n.Testing.fixtureUserVAddr va) == none)
          assertBool "RETIRED: the bare delete — no finalisation — left all three tables and the mapping in place"
            (match cspaceDeleteSlot at15 st3 with
             | .ok ((), r) => slotsOf r 980 == slotsOf st3 980 &&
                 mappedPaddr r one (SeLe4n.Testing.fixtureUserVAddr va) == some (carveUtBase + SeLe4n.pageBytes)
             | .error _ => false)
          assertBool "a table left with a stale record installs again, at the shallowest missing level"
            (match dispatchSyscall (decodeTableMap 16 12 va) carveOwner sDel with
             | .ok ((), r) => slotsOf r 980 == some [(1, 984)] &&
                 (installOf r 984).map (·.level) == some 1
             | .error _ => false)
          assertBool "a CNode holding an installed table's capability is not retyped in place"
            (match st3.objects[carveCn]? with
             | some (.cnode cn) => Architecture.cnodeHoldsInstalledPageTableCap st3 cn
             | _ => false)
        match runAll st3 [decodeUnmapVia 12 1 va, decodeTableUnmap 17] with
        | .error e => assertBool s!"unmapping the frame, then the level-3 table, succeeds (got {repr e})" false
        | .ok st4 => do
          assertBool "the level-3 slot is gone and the table is installed nowhere"
            (slotsOf st4 980 == some [(1, 983), (2, 984)] && installOf st4 985 == none)
          assertBool "unmapping a table installed nowhere succeeds and changes nothing"
            (match dispatchSyscall (decodeTableUnmap 17) carveOwner st4 with
             | .ok ((), s) => slotsOf s 980 == slotsOf st4 980 && installOf s 985 == none
             | .error _ => false)
          -- A table carved from a CHILD untyped and installed in the parent's
          -- root: revoking the child's capability destroys the table's last
          -- capability, so the table leaves the root and the child resets alone.
          match runAll st4
              [decodeCarve slotUtRetype (untypedTagOfSize 12) 990 slotOwnCnRW 19,
               decodeCarve 19 pageTableTag 991 slotOwnCnRW 20,
               decodeTableMap 20 12 (2 ^ 39)] with
          | .error e => assertBool s!"carving a child untyped and a table from it, and installing it, succeeds (got {repr e})" false
          | .ok stA => do
            assertBool "RETIRED: the bare revocation leaves the child's table in the surviving root"
              (match cspaceRevokeCdt { cnode := carveCn, slot := SeLe4n.Slot.ofNat 19 } stA with
               | .ok (_, r) => (slotsOf r 980).any (·.contains (1, 991))
               | .error _ => false)
            match dispatchSyscall (decodeRevoke 19) carveOwner stA with
            | .error e => assertBool s!"revoking the child's capability succeeds (got {repr e})" false
            | .ok ((), st5) => do
              let childIds := match st5.getUntyped? (SeLe4n.ObjId.ofNat 990) with
                | some u => (untypedCarvedSubtree st5 u).getD []
                | none => []
              assertBool "the revocation took the child's table out of the parent's root"
                (slotsOf st5 980 == slotsOf st4 980 &&
                 !Architecture.pageTableInstallLive st5 (SeLe4n.ObjId.ofNat 991))
              assertBool "so the child's subtree is unreferenced and closed"
                (childIds == [SeLe4n.ObjId.ofNat 991] && carvedSubtreeUnreferenced st5 childIds &&
                 carvedSubtreeInstallsClosed st5 childIds)
              match dispatchSyscall (decodeReset 19) carveOwner st5 with
              | .error e => assertBool s!"resetting the child alone succeeds (got {repr e})" false
              | .ok ((), st5r) => do
                assertBool "the child's table is retired and the parent's root is untouched"
                  ((st5r.objects[SeLe4n.ObjId.ofNat 991]?).isNone && slotsOf st5r 980 == slotsOf st5 980)
                -- The boundary the reset still enforces: an address space carved
                -- from the child holding a table carved from the parent, whose
                -- capability survives the child's revocation.
                match runAll st5r
                    [decodeCarve 19 vspaceRootTag 993 slotOwnCnRW 21,
                     decodeCarve slotUtRetype pageTableTag 994 slotOwnCnRW 22,
                     decodeTableMap 22 21 va,
                     decodeRevoke 19] with
                | .error e => assertBool s!"carving a root from the child, installing a parent table in it, and revoking the child succeeds (got {repr e})" false
                | .ok st6 => do
                  let childIds6 := match st6.getUntyped? (SeLe4n.ObjId.ofNat 990) with
                    | some u => (untypedCarvedSubtree st6 u).getD []
                    | none => []
                  assertBool "CONTROL: nothing names the child's root any more (the refusal below is the boundary's)"
                    (childIds6 == [SeLe4n.ObjId.ofNat 993] && carvedSubtreeUnreferenced st6 childIds6)
                  assertBool "the child's subtree is not closed: its root holds a surviving table"
                    (!carvedSubtreeInstallsClosed st6 childIds6)
                  assertBool "so resetting the child alone is refused (revocationRequired)"
                    (isErr .revocationRequired (dispatchSyscall (decodeReset 19) carveOwner st6))
                  match runAll st6 [decodeRevoke slotUtRetype, decodeReset slotUtRetype] with
                  | .error e => assertBool s!"CONTROL: the parent's reset, taking roots and tables together, succeeds (got {repr e})" false
                  | .ok st7 =>
                    assertBool "CONTROL: the roots, every table, the frame and the child are retired"
                      ([980, 982, 983, 984, 985, 986, 990, 993, 994].all
                        (fun n => (st7.objects[SeLe4n.ObjId.ofNat n]?).isNone))

-- ============================================================================
-- §5l  WS-BP BP7.2 (`v0.36.15`) — the physical writes a transition records
-- ============================================================================

/-- The writes a step appended to the ledger. -/
private def recordedBy (before after : SystemState) : List Architecture.PhysicalWrite :=
  after.pendingPhysicalWrites.drop before.pendingPhysicalWrites.length

private def store (entry : Nat) (value : UInt64) : Architecture.PhysicalWrite :=
  .storeDescriptor (SeLe4n.PAddr.ofNat entry) value

private def zero (page : Nat) : Architecture.PhysicalWrite :=
  .zeroPage (SeLe4n.PAddr.ofNat page)

/-- A table descriptor, spelled from the architecture rather than from the model's
encoder: the page's address and `0b11` (ARM ARM D8.3.1). -/
private def tableDesc (page : Nat) : UInt64 := page.toUInt64 ||| (0b11 : UInt64)

private def runPhysicalWriteChecks : IO Unit := do
  IO.println "-- §5l the physical writes a transition records (WS-BP BP7.2)"
  let st := tableScenario
  let va : Nat := 0x70000
  -- Carve order fixes each page: the root at the untyped's base, then the
  -- frame, then the four tables, one page each.
  let root := carveUtBase
  let frame := carveUtBase + SeLe4n.pageBytes
  let l1 := carveUtBase + 2 * SeLe4n.pageBytes
  let l2 := carveUtBase + 3 * SeLe4n.pageBytes
  let l3 := carveUtBase + 4 * SeLe4n.pageBytes
  let spare := carveUtBase + 5 * SeLe4n.pageBytes
  assertBool "the scenario starts with nothing owed"
    (st.pendingPhysicalWrites == [])
  match runAll st
      [decodeCarve slotUtRetype vspaceRootTag 980 slotOwnCnRW 12,
       decodeCarve slotUtRetype frameTag 982 slotOwnCnRW 14,
       decodeCarve slotUtRetype pageTableTag 983 slotOwnCnRW 15,
       decodeCarve slotUtRetype pageTableTag 984 slotOwnCnRW 16,
       decodeCarve slotUtRetype pageTableTag 985 slotOwnCnRW 17,
       decodeCarve slotUtRetype pageTableTag 986 slotOwnCnRW 18] with
  | .error e => assertBool s!"carving a root, a frame and four tables succeeds (got {repr e})" false
  | .ok st1 => do
    assertBool "every carved page is zeroed in memory, in carve order"
      (recordedBy st st1 == [zero root, zero frame, zero l1, zero l2, zero l3, zero spare])
    -- v0.36.32: each zeroing owes its own page's clean to the Point of
    -- Unification and a domain-wide `IC IALLUIS` — the carved frame could be
    -- mapped executable next, and the zeroes must reach the instruction side
    -- before its previous contents can be fetched.  A write that owed nothing
    -- (the pre-v0.36.32 ledger) answers `none` here and fails the check.
    assertBool "every carve zeroing owes a clean-to-PoU of exactly its own page"
      ((recordedBy st st1).all fun w =>
        match w with
        | .zeroPage base =>
          w.icacheMaintenance
            == some (Architecture.ICacheInvalidation.cleanRangeIallu base SeLe4n.pageBytes)
        | _ => false)
    assertBool "and a descriptor store owes none (only a zeroing can precede a fetch)"
      ((store (root + 8) (tableDesc l1)).icacheMaintenance == none)
    match dispatchSyscall (decodeTableMap 15 12 va) carveOwner st1 with
    | .error e => assertBool s!"installing the level-1 table succeeds (got {repr e})" false
    | .ok ((), st2) => do
      -- 2^39 + 0x70000: level-0 index 1 (entry 0 is the kernel window).
      assertBool "a level-1 install stores its table descriptor at entry 1 of the root's page"
        (recordedBy st1 st2 == [store (root + 8) (tableDesc l1)])
      match runAll st2 [decodeTableMap 16 12 va, decodeTableMap 17 12 va] with
      | .error e => assertBool s!"installing levels 2 and 3 succeeds (got {repr e})" false
      | .ok st3 => do
        assertBool "levels 2 and 3 store at entry 0 of the table above each"
          (recordedBy st2 st3 == [store l1 (tableDesc l2), store l2 (tableDesc l3)])
        match dispatchSyscall (decodeMapVia 12 1 va 14 permsRWUC) carveOwner st3 with
        | .error e => assertBool s!"mapping the frame succeeds (got {repr e})" false
        | .ok ((), st4) => do
          -- The page descriptor, bit by bit: the frame's address; valid page
          -- (0b11); AttrIndx 0 (Normal); AP 0b01 (EL0 read/write); SH inner;
          -- AF; nG (ASID-tagged); PXN (the kernel never executes it); UXN
          -- (not executable — no execute right).
          let bit (n : UInt64) : UInt64 := (1 : UInt64) <<< n
          let desc : UInt64 := frame.toUInt64 ||| (0b11 : UInt64) ||| bit 6 ||| (0b11 <<< (8 : UInt64)) |||
            bit 10 ||| bit 11 ||| bit 53 ||| bit 54
          assertBool "a mapping stores its page descriptor at the frame's level-3 entry (0x70 → +0x380)"
            (recordedBy st3 st4 == [store (l3 + 0x380) desc])
          match dispatchSyscall (decodeUnmapVia 12 1 va) carveOwner st4 with
          | .error e => assertBool s!"unmapping the frame succeeds (got {repr e})" false
          | .ok ((), st5) => do
            assertBool "an unmap stores the invalid descriptor at the same entry"
              (recordedBy st4 st5 == [store (l3 + 0x380) 0])
            match dispatchSyscall (decodeTableUnmap 17) carveOwner st5 with
            | .error e => assertBool s!"unmapping the level-3 table succeeds (got {repr e})" false
            | .ok ((), st6) =>
              assertBool "a table unmap clears its entry in the table above, then drops the ASID's cached walks"
                (recordedBy st5 st6 == [store l2 0, .invalidateAsid (SeLe4n.ASID.ofNat 1)])
          match dispatchSyscall (decodeDelete 15) carveOwner st4 with
          | .error e => assertBool s!"deleting the level-1 table's last capability succeeds (got {repr e})" false
          | .ok ((), sDel) => do
            let ws := recordedBy st4 sDel
            assertBool "destroying a table's last capability clears the root's entry for it"
              (ws.contains (store (root + 8) 0))
            assertBool "...zeroes the three table pages it takes out, so a stale one re-installs empty"
              ([l1, l2, l3].all (fun p => ws.contains (zero p)))
            assertBool "...and ends by dropping the ASID's cached walks"
              (ws.getLast? == some (.invalidateAsid (SeLe4n.ASID.ofNat 1)))
            assertBool "the untouched spare table's page is not rewritten"
              (!ws.contains (zero spare))
    -- A root with no table page records no descriptor: the walker has no page
    -- to read, so there is nothing to make agree.
    assertBool "a root that owns no page records no descriptor store"
      (match storeObject carveVsp (.vspaceRoot { asid := SeLe4n.ASID.ofNat 3, mappings := {} }) st1 with
       | .ok ((), s) =>
           match s.getVSpaceRoot? carveVsp with
           | some r => Architecture.mappingStore? s r (SeLe4n.Testing.fixtureUserVAddr va) == none &&
                       Architecture.slotStore? s r 1 1 == none
           | none => false
       | .error _ => false)
  -- The thread-translation operands: a thread whose root owns a page and a
  -- non-kernel ASID installs that page and ASID; any other runs under the
  -- kernel's translation, `(0, 0)`.
  match dispatchSyscall (decodeCarve slotUtRetype vspaceRootTag 980 slotOwnCnRW 12) carveOwner spaceScenario with
  | .error e => assertBool s!"carving a root in the §5j scenario succeeds (got {repr e})" false
  | .ok ((), sp1) => do
    assertBool "a thread in the fixture's mappable root installs that root's page and ASID"
      (Architecture.threadTranslationOperands sp1 spaceWorker ==
        ((0x7D000 : UInt64), carveAsid.toNat.toUInt64))
    assertBool "a thread whose root owns no page runs under the kernel's translation (0, 0)"
      (match storeObject carveVsp (.vspaceRoot { asid := carveAsid, mappings := {} }) sp1 with
       | .ok ((), s) => Architecture.threadTranslationOperands s spaceWorker == (0, 0)
       | .error _ => false)
    assertBool "a thread id that resolves to no thread runs under the kernel's translation (0, 0)"
      (Architecture.threadTranslationOperands sp1 ⟨99999⟩ == (0, 0))
    match dispatchSyscall (decodeSetSpace slotWorkerTcb slotOwnCnGrant 12) carveOwner sp1 with
    | .error e => assertBool s!"moving the worker into the carved root succeeds (got {repr e})" false
    | .ok ((), sp2) =>
      assertBool "moved into the carved root, it installs that root's page under ASID 1"
        (Architecture.threadTranslationOperands sp2 spaceWorker == (carveUtBase.toUInt64, (1 : UInt64)))

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
  runChildUntypedChecks
  runInPlaceVSpaceRootChecks
  runCarvedRootChecks
  runSetSpaceChecks
  runPageTableChecks
  runPhysicalWriteChecks
  runFrameFinaliseChecks
  runAuthorizedChecks
  IO.println "===================================================="
  IO.println "All VSpace capability-binding checks PASS."

end SeLe4n.Testing.VSpaceCapabilityBinding

def main : IO Unit :=
  SeLe4n.Testing.VSpaceCapabilityBinding.runVSpaceCapabilityBindingChecks
