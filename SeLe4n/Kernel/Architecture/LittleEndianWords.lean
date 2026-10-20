-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/


/-!
# Little-endian words in a byte buffer

The kernel's word buffers — the entry's overflow words the HAL captures, the
physical writes a transition owes the HAL — are `ByteArray`s of 64-bit
little-endian words, the layout the HAL reads and writes them in.  `le64At`
reads a word, `setLe64` writes one in place (an unshared buffer is updated
where it lies), and the lemmas here say a write reads back and leaves every
other word as it was.
-/

namespace SeLe4n.Kernel.Architecture

/-- The little-endian word at byte `off` of `b` (a byte past the end reads 0). -/
@[inline] def le64At (b : ByteArray) (off : Nat) : UInt64 :=
  (b.get! off).toUInt64 ||| ((b.get! (off + 1)).toUInt64 <<< 8) |||
    ((b.get! (off + 2)).toUInt64 <<< 16) ||| ((b.get! (off + 3)).toUInt64 <<< 24) |||
    ((b.get! (off + 4)).toUInt64 <<< 32) ||| ((b.get! (off + 5)).toUInt64 <<< 40) |||
    ((b.get! (off + 6)).toUInt64 <<< 48) ||| ((b.get! (off + 7)).toUInt64 <<< 56)

/-- Write `x` as the little-endian word at byte `off` of `b`, byte by byte in
place (a byte past the end is not written). -/
@[inline] def setLe64 (b : ByteArray) (off : Nat) (x : UInt64) : ByteArray :=
  ((((((((b.set! off x.toUInt8).set! (off + 1) (x >>> 8).toUInt8).set! (off + 2)
    (x >>> 16).toUInt8).set! (off + 3) (x >>> 24).toUInt8).set! (off + 4)
    (x >>> 32).toUInt8).set! (off + 5) (x >>> 40).toUInt8).set! (off + 6)
    (x >>> 48).toUInt8).set! (off + 7) (x >>> 56).toUInt8)

theorem ByteArray.get!_set! (b : ByteArray) (i j : Nat) (v : UInt8) :
    (b.set! i v).get! j = if i = j ∧ i < b.size then v else b.get! j := by
  cases b with
  | mk d =>
  simp only [ByteArray.set!, ByteArray.get!, Array.set!_eq_setIfInBounds, ByteArray.size]
  by_cases hj : j < d.size
  · rw [getElem!_pos (d.setIfInBounds i v) j (by simpa using hj), getElem!_pos d j hj,
      Array.getElem_setIfInBounds (by simpa using hj)]
    by_cases h : i = j <;> simp [h, hj]
  · rw [getElem!_neg (d.setIfInBounds i v) j (by simpa using hj), getElem!_neg d j hj]
    split
    · next h => omega
    · rfl

@[simp] theorem ByteArray.size_set! (b : ByteArray) (i : Nat) (v : UInt8) :
    (b.set! i v).size = b.size := by
  cases b; simp [ByteArray.set!, ByteArray.size, Array.set!_eq_setIfInBounds]

@[simp] theorem size_setLe64 (b : ByteArray) (off : Nat) (x : UInt64) :
    (setLe64 b off x).size = b.size := by
  simp [setLe64]

theorem getLsbD_umod256 (y : BitVec 64) (j : Nat) :
    (y % 256#64).getLsbD j = (decide (j < 8) && y.getLsbD j) := by
  simp only [BitVec.getLsbD, BitVec.toNat_umod, BitVec.toNat_ofNat]
  rw [show (256 % 2^64) = 2^8 from rfl, Nat.testBit_mod_two_pow]

theorem getElem_umod256 (y : BitVec 64) (j : Nat) (h : j < 64) :
    (y % 256#64)[j] = (decide (j < 8) && y[j]) := by
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]; exact getLsbD_umod256 y j

/-- Bit `i` of the byte of `x` at bit `k`, put back at bit `k`. -/
theorem getLsbD_byteAt (x : UInt64) (k : UInt64) (hk : k.toNat < 64) (i : Nat) (hi : i < 64) :
    (((x >>> k).toUInt8.toUInt64 <<< k)).toBitVec.getLsbD i =
      (decide (k.toNat ≤ i ∧ i < k.toNat + 8) && x.toBitVec.getLsbD i) := by
  simp [hi, Nat.mod_eq_of_lt hk]
  by_cases h : k.toNat ≤ i
  · have h' : ¬ i < k.toNat := by omega
    simp only [h', decide_false, Bool.not_false, Bool.true_and, h, decide_true]
    rw [getElem_umod256 _ _ (by omega), BitVec.getElem_ushiftRight, Nat.add_sub_cancel' h]
    by_cases h2 : i < k.toNat + 8
    · simp [h2, show i - k.toNat < 8 by omega, hi]
    · simp [h2, show ¬ i - k.toNat < 8 by omega]
  · simp [h, show i < k.toNat by omega]

theorem getLsbD_byteAt0 (x : UInt64) (i : Nat) :
    (x.toUInt8.toUInt64).toBitVec.getLsbD i = (decide (i < 8) && x.toBitVec.getLsbD i) := by
  have := getLsbD_byteAt x 0 (by decide) i
  by_cases hi : i < 64
  · have h := this hi
    simp only [UInt64.shiftLeft_zero, UInt64.shiftRight_zero] at h
    rw [h]; simp
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 64 ≤ i)]

/-- A word's eight bytes, put back in place, are the word. -/
theorem le64_bytes (x : UInt64) : x.toUInt8.toUInt64 ||| ((x >>> 8).toUInt8.toUInt64 <<< 8) |||
    ((x >>> 16).toUInt8.toUInt64 <<< 16) ||| ((x >>> 24).toUInt8.toUInt64 <<< 24) |||
    ((x >>> 32).toUInt8.toUInt64 <<< 32) ||| ((x >>> 40).toUInt8.toUInt64 <<< 40) |||
    ((x >>> 48).toUInt8.toUInt64 <<< 48) ||| ((x >>> 56).toUInt8.toUInt64 <<< 56) = x := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt64.toBitVec_or, BitVec.getLsbD_or, getLsbD_byteAt0,
    getLsbD_byteAt x 8 (by decide) i hi, getLsbD_byteAt x 16 (by decide) i hi,
    getLsbD_byteAt x 24 (by decide) i hi, getLsbD_byteAt x 32 (by decide) i hi,
    getLsbD_byteAt x 40 (by decide) i hi, getLsbD_byteAt x 48 (by decide) i hi,
    getLsbD_byteAt x 56 (by decide) i hi]
  cases x.toBitVec.getLsbD i <;> simp <;> omega

/-- A byte outside the written word is unchanged. -/
theorem get!_setLe64_of_lt (b : ByteArray) (off j : Nat) (x : UInt64)
    (h : j < off ∨ off + 8 ≤ j) : (setLe64 b off x).get! j = b.get! j := by
  simp only [setLe64, ByteArray.get!_set!]
  repeat (rw [if_neg (by omega)])

/-- The word just written reads back. -/
theorem le64At_setLe64_same (b : ByteArray) (off : Nat) (x : UInt64)
    (h : off + 8 ≤ b.size) : le64At (setLe64 b off x) off = x := by
  simp only [le64At, setLe64, ByteArray.get!_set!, ByteArray.size_set!]
  simp only [show off + 1 ≠ off from by omega, show off + 2 ≠ off from by omega,
    show off + 3 ≠ off from by omega, show off + 4 ≠ off from by omega,
    show off + 5 ≠ off from by omega, show off + 6 ≠ off from by omega,
    show off + 7 ≠ off from by omega, show off + 2 ≠ off + 1 from by omega,
    show off + 3 ≠ off + 1 from by omega, show off + 4 ≠ off + 1 from by omega,
    show off + 5 ≠ off + 1 from by omega, show off + 6 ≠ off + 1 from by omega,
    show off + 7 ≠ off + 1 from by omega, show off + 3 ≠ off + 2 from by omega,
    show off + 4 ≠ off + 2 from by omega, show off + 5 ≠ off + 2 from by omega,
    show off + 6 ≠ off + 2 from by omega, show off + 7 ≠ off + 2 from by omega,
    show off + 4 ≠ off + 3 from by omega, show off + 5 ≠ off + 3 from by omega,
    show off + 6 ≠ off + 3 from by omega, show off + 7 ≠ off + 3 from by omega,
    show off + 5 ≠ off + 4 from by omega, show off + 6 ≠ off + 4 from by omega,
    show off + 7 ≠ off + 4 from by omega, show off + 6 ≠ off + 5 from by omega,
    show off + 7 ≠ off + 5 from by omega, show off + 7 ≠ off + 6 from by omega,
    show off < b.size from by omega, show off + 1 < b.size from by omega,
    show off + 2 < b.size from by omega, show off + 3 < b.size from by omega,
    show off + 4 < b.size from by omega, show off + 5 < b.size from by omega,
    show off + 6 < b.size from by omega, show off + 7 < b.size from by omega,
    and_self, and_true, if_true, if_false]
  exact le64_bytes x

/-- A word that does not overlap the written one is unchanged. -/
theorem le64At_setLe64_of_disjoint (b : ByteArray) (off j : Nat) (x : UInt64)
    (h : j + 8 ≤ off ∨ off + 8 ≤ j) : le64At (setLe64 b off x) j = le64At b j := by
  simp only [le64At]
  repeat (rw [get!_setLe64_of_lt b off _ x (by omega)])

end SeLe4n.Kernel.Architecture
