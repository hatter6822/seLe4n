/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
-/
import SeLe4n.Testing.Helpers

/-!
# Lean runtime conformance — the shared fixture (WS-BP BP2.2)

The kernel links its own Lean runtime (`rust/sele4n-hal/src/lean_runtime/`)
instead of upstream's C++ `libleanrt`.  Every primitive it ports must answer as
upstream answers, and the only authority on what upstream answers is upstream
running.  This suite *is* that: it is an ordinary Lean executable, linked with
the toolchain's own runtime, and it computes each primitive over an operand
corpus chosen at the boundaries the representation changes at — the small/big
`Nat` edge at `2^63`, the small/big `Int` edge at `±2^31`, limb edges at
`2^64` and `2^128`, signs, zero divisors, UTF-8 widths one to four, positions
inside a character and past the end.

The lines it produces must equal `tests/fixtures/lean_runtime_conformance.expected`
byte for byte; the Rust tests (`lean_runtime::conformance`) read the same file
and recompute every line with the kernel's runtime.  A disagreement on either
side names the line.

Numbers are hexadecimal (`-0x…` for a negative `Int`), strings and byte arrays
their bytes in hexadecimal (`-` for empty), and every operand is referred to by
its index in the corpus lines, which precede every result that uses them.
-/

namespace SeLe4n.Testing.LeanRuntimeConformance

private def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

private def hexInt (i : Int) : String :=
  if i < 0 then "-" ++ hex i.natAbs else hex i.toNat

private def hexByte (b : UInt8) : String :=
  let d := Nat.toDigits 16 b.toNat
  String.ofList (if d.length == 1 then '0' :: d else d)

private def hexBytes (bs : List UInt8) : String :=
  if bs.isEmpty then "-" else String.join (bs.map hexByte)

private def hexString (s : String) : String := hexBytes s.toUTF8.toList

/-- The `Nat` corpus: both sides of every representation edge. -/
def natCorpus : List Nat :=
  [0, 1, 2, 3, 10, 2^31 - 1, 2^31, 2^32 - 1, 2^32, 2^62, 2^63 - 1, 2^63,
   2^63 + 1, 2^64 - 1, 2^64, 2^64 + 1, 2^96 + 2^32 + 7, 2^127, 2^128 - 1,
   2^128, 3^80, 3^80 + 1, 2^200 - 1, 10^40 + 12345678901234567]

/-- The `Int` corpus: signs on both sides of the `±2^31` and limb edges. -/
def intCorpus : List Int :=
  [0, 1, -1, 7, -7, 2^31 - 1, -(2^31), 2^31, -(2^31) - 1, 2^63, -(2^63),
   2^64 + 1, -(2^64) - 1, 3^80, -(3^80)]

/-- Shift amounts and exponents. -/
def smallCorpus : List Nat := [0, 1, 2, 7, 63, 64, 65, 127, 200]

def natLines : List String := Id.run do
  let mut out : Array String := #[]
  for (a, i) in natCorpus.zipIdx do
    out := out.push s!"nat {i} {hex a}"
  for (a, i) in natCorpus.zipIdx do
    for (b, j) in natCorpus.zipIdx do
      out := out.push s!"nat_add {i} {j} {hex (a + b)}"
      out := out.push s!"nat_sub {i} {j} {hex (a - b)}"
      out := out.push s!"nat_mul {i} {j} {hex (a * b)}"
      out := out.push s!"nat_div {i} {j} {hex (a / b)}"
      out := out.push s!"nat_mod {i} {j} {hex (a % b)}"
      out := out.push s!"nat_land {i} {j} {hex (a &&& b)}"
      out := out.push s!"nat_lor {i} {j} {hex (a ||| b)}"
      out := out.push s!"nat_xor {i} {j} {hex (a ^^^ b)}"
      out := out.push s!"nat_gcd {i} {j} {hex (Nat.gcd a b)}"
      out := out.push s!"nat_cmp {i} {j} {if a < b then "lt" else if a == b then "eq" else "gt"}"
    for s in smallCorpus do
      out := out.push s!"nat_shiftl {i} {s} {hex (a <<< s)}"
      out := out.push s!"nat_shiftr {i} {s} {hex (a >>> s)}"
    for e in [0, 1, 2, 3, 7] do
      out := out.push s!"nat_pow {i} {e} {hex (a ^ e)}"
    out := out.push s!"nat_log2 {i} {hex (Nat.log2 a)}"
    out := out.push s!"nat_low {i} {(UInt8.ofNat a).toNat} {(UInt16.ofNat a).toNat} {(UInt32.ofNat a).toNat} {(UInt64.ofNat a).toNat} {(USize.ofNat a).toNat}"
    out := out.push s!"nat_decimal {i} {toString a}"
  return out.toList

def intLines : List String := Id.run do
  let mut out : Array String := #[]
  for (a, i) in intCorpus.zipIdx do
    out := out.push s!"int {i} {hexInt a}"
  for (a, i) in intCorpus.zipIdx do
    for (b, j) in intCorpus.zipIdx do
      out := out.push s!"int_add {i} {j} {hexInt (a + b)}"
      out := out.push s!"int_sub {i} {j} {hexInt (a - b)}"
      out := out.push s!"int_mul {i} {j} {hexInt (a * b)}"
      out := out.push s!"int_tdiv {i} {j} {hexInt (Int.tdiv a b)}"
      out := out.push s!"int_tmod {i} {j} {hexInt (Int.tmod a b)}"
      out := out.push s!"int_ediv {i} {j} {hexInt (a / b)}"
      out := out.push s!"int_emod {i} {j} {hexInt (a % b)}"
      out := out.push s!"int_cmp {i} {j} {if a < b then "lt" else if a == b then "eq" else "gt"}"
    out := out.push s!"int_neg {i} {hexInt (-a)}"
    out := out.push s!"int_low {i} {(Int8.ofInt a).toInt} {(Int16.ofInt a).toInt} {(Int32.ofInt a).toInt} {(Int64.ofInt a).toInt} {(ISize.ofInt a).toInt}"
    out := out.push s!"int_to_nat {i} {hex a.toNat}"
  return out.toList

/-- The string corpus: every UTF-8 width, alone and mixed. -/
def stringCorpus : List String :=
  ["", "a", "hello", "héllo", "日本", "😀!", "aé日😀z"]

def charCorpus : List Char := ['x', 'é', '日', '😀']

def stringLines : List String := Id.run do
  let mut out : Array String := #[]
  for (s, i) in stringCorpus.zipIdx do
    out := out.push s!"str {i} {hexString s}"
  for (c, k) in charCorpus.zipIdx do
    out := out.push s!"char {k} {c.toNat}"
  for (s, i) in stringCorpus.zipIdx do
    out := out.push s!"str_hash {i} {s.hash.toNat}"
    out := out.push s!"str_length {i} {s.length}"
    for p in List.range (s.utf8ByteSize + 2) do
      let pos : String.Pos.Raw := ⟨p⟩
      out := out.push s!"str_get {i} {p} {(String.Pos.Raw.get s pos).toNat}"
      out := out.push s!"str_next {i} {p} {(String.Pos.Raw.next s pos).byteIdx}"
      out := out.push s!"str_valid {i} {p} {decide (String.Pos.Raw.isValid s pos)}"
      for (c, k) in charCorpus.zipIdx do
        out := out.push s!"str_set {i} {p} {k} {hexString (String.Pos.Raw.set s pos c)}"
      for q in List.range (s.utf8ByteSize + 2) do
        out := out.push s!"str_extract {i} {p} {q} {hexString (String.Pos.Raw.extract s pos ⟨q⟩)}"
    for (c, k) in charCorpus.zipIdx do
      out := out.push s!"str_push {i} {k} {hexString (s.push c)}"
    for (t, j) in stringCorpus.zipIdx do
      out := out.push s!"str_append {i} {j} {hexString (s ++ t)}"
      out := out.push s!"str_lt {i} {j} {decide (s < t)}"
  return out.toList

/-- Byte arrays and 64-bit words for the two hash functions. -/
def bytesCorpus : List (List UInt8) :=
  [[], [0], [1, 2, 3], [0xff, 0x00, 0x7f, 0x80, 0x01, 0x02, 0x03],
   [1, 2, 3, 4, 5, 6, 7, 8], [1, 2, 3, 4, 5, 6, 7, 8, 9],
   (List.range 37).map (fun n => UInt8.ofNat (n * 7 + 3))]

def wordCorpus : List UInt64 := [0, 1, 11, 0xc6a4a7935bd1e995, 0xffffffffffffffff, 1234567890123]

def hashLines : List String := Id.run do
  let mut out : Array String := #[]
  for (b, i) in bytesCorpus.zipIdx do
    out := out.push s!"bytes {i} {hexBytes b}"
    out := out.push s!"bytes_hash {i} {(ByteArray.mk b.toArray).hash.toNat}"
  for x in wordCorpus do
    for y in wordCorpus do
      out := out.push s!"mix_hash {x.toNat} {y.toNat} {(mixHash x y).toNat}"
  return out.toList

/-- Facts about the environment the runtime reproduces by construction. -/
def environmentLines : List String :=
  [s!"platform_nbits {System.Platform.numBits}",
   s!"io_error_unsupported_operation_ctor {(IO.Error.unsupportedOperation 38 "").ctorIdx}"]

def fixtureLines : List String :=
  natLines ++ intLines ++ stringLines ++ hashLines ++ environmentLines

private def fixturePath : String := "tests/fixtures/lean_runtime_conformance.expected"

end SeLe4n.Testing.LeanRuntimeConformance

open SeLe4n.Testing.LeanRuntimeConformance in
def main (args : List String) : IO Unit := do
  if args == ["--emit"] then
    for l in fixtureLines do
      IO.println l
    return
  SeLe4n.Testing.checkSharedFixture "Lean runtime conformance" fixturePath
    "`lean_runtime::conformance` in rust/sele4n-hal" fixtureLines
  IO.println s!"  {fixtureLines.length} primitive results checked against the upstream runtime"
