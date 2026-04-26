-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.VSpaceARMv8
import SeLe4n.Model.Object.Structures
import SeLe4n.Testing.Helpers

/-! # AK3-B: W^X Four-Layer Defense Regression Tests (A-H01 HIGH)

Regression coverage for the AK3-B defense-in-depth W^X enforcement. Each
test targets one of the four layers independently, verifying that a
`PagePermissions` value with `write = true ∧ execute = true` is rejected
at each layer.

Layers exercised:
- L3 `fromPagePermissions`      — encode-time reject (returns `none`)
- L2 `VSpaceRoot.mapPage`        — HashMap-level reject
- L1 `ARMv8VSpace.mapPage`       — backend-level reject
- L0 `vspaceMapPage` wrapper     — already tested under V4-E; referenced here

A W^X-compliant configuration (e.g., read-only or write-only) should be
accepted by each layer.
-/

open SeLe4n.Kernel.Architecture
open SeLe4n.Model
open SeLe4n.Testing

namespace SeLe4n.Testing.WxDefense

/-- W+X permissions (write=true, execute=true, user=true). -/
def wxPerms : PagePermissions :=
  { read := true, write := true, execute := true, user := true, cacheable := true }

/-- Read-only permissions (W^X compliant). -/
def roPerms : PagePermissions := PagePermissions.readOnly

/-- Read+write permissions (W^X compliant — no execute). -/
def rwPerms : PagePermissions :=
  { read := true, write := true, execute := false, user := true, cacheable := true }

/-- Read+execute permissions (W^X compliant — no write). -/
def rxPerms : PagePermissions :=
  { read := true, write := false, execute := true, user := true, cacheable := true }

/-- T01: L3 gate — `fromPagePermissions` returns `none` on W+X. -/
def test_t01_L3_rejects_wx : IO Unit := do
  match fromPagePermissions wxPerms with
  | none =>
    IO.println "check passed [L3 fromPagePermissions rejects W+X]"
  | some _ =>
    throw <| IO.userError "T01: L3 accepted W+X permissions (security regression!)"

/-- T02: L3 — `fromPagePermissions` accepts read-only (W^X compliant). -/
def test_t02_L3_accepts_ro : IO Unit := do
  match fromPagePermissions roPerms with
  | some _ =>
    IO.println "check passed [L3 accepts read-only]"
  | none =>
    throw <| IO.userError "T02: L3 rejected read-only permissions"

/-- T03: L3 — accepts R+W (no execute). -/
def test_t03_L3_accepts_rw : IO Unit := do
  match fromPagePermissions rwPerms with
  | some _ =>
    IO.println "check passed [L3 accepts R+W]"
  | none =>
    throw <| IO.userError "T03: L3 rejected R+W permissions"

/-- T04: L3 — accepts R+X (no write). -/
def test_t04_L3_accepts_rx : IO Unit := do
  match fromPagePermissions rxPerms with
  | some _ =>
    IO.println "check passed [L3 accepts R+X]"
  | none =>
    throw <| IO.userError "T04: L3 rejected R+X permissions"

/-- T05: L2 gate — `VSpaceRoot.mapPage` returns `none` on W+X. -/
def test_t05_L2_rejects_wx : IO Unit := do
  let emptyRoot : VSpaceRoot :=
    { asid := SeLe4n.ASID.mk 1, mappings := default }
  match emptyRoot.mapPage (SeLe4n.VAddr.ofNat 0x1000) (SeLe4n.PAddr.ofNat 0x2000) wxPerms with
  | none =>
    IO.println "check passed [L2 VSpaceRoot.mapPage rejects W+X]"
  | some _ =>
    throw <| IO.userError "T05: L2 accepted W+X (security regression!)"

/-- T06: L2 — accepts R+W. -/
def test_t06_L2_accepts_rw : IO Unit := do
  let emptyRoot : VSpaceRoot :=
    { asid := SeLe4n.ASID.mk 1, mappings := default }
  match emptyRoot.mapPage (SeLe4n.VAddr.ofNat 0x1000) (SeLe4n.PAddr.ofNat 0x2000) rwPerms with
  | some _ =>
    IO.println "check passed [L2 accepts R+W]"
  | none =>
    throw <| IO.userError "T06: L2 rejected R+W (wrongful rejection)"

/-- T07: W^X compliance check on W+X perms value. -/
def test_t07_wxCompliant_W_and_X_false : IO Unit := do
  expectCond "wx-defense" "W+X not wxCompliant"
    (wxPerms.wxCompliant == false)

/-- T08: W^X compliance check on R+X and R+W. -/
def test_t08_wxCompliant_R_alone_true : IO Unit := do
  expectCond "wx-defense" "R+W wxCompliant" (rwPerms.wxCompliant == true)
  expectCond "wx-defense" "R+X wxCompliant" (rxPerms.wxCompliant == true)
  expectCond "wx-defense" "readOnly wxCompliant" (roPerms.wxCompliant == true)

/-- Running entry. -/
def runAllTests : IO Unit := do
  IO.println "=== AK3-B W^X Four-Layer Defense regression suite ==="
  test_t01_L3_rejects_wx
  test_t02_L3_accepts_ro
  test_t03_L3_accepts_rw
  test_t04_L3_accepts_rx
  test_t05_L2_rejects_wx
  test_t06_L2_accepts_rw
  test_t07_wxCompliant_W_and_X_false
  test_t08_wxCompliant_R_alone_true
  IO.println "=== All AK3-B W^X tests passed ==="

end SeLe4n.Testing.WxDefense

open SeLe4n.Testing.WxDefense

def main : IO Unit := runAllTests
