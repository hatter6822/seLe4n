-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

/-!
# Packed strings — kernel-cheap distinctness for the theorem inventories

Every theorem inventory (`perCoreCbsTheorems`, `lockSetTheorems`, …) proves
that its identifiers and its descriptions are pairwise distinct, and the
project rule is that the proof is the kernel's `decide`, never
`native_decide`.  Deciding `Nodup` over `String` literals is what that rule
cost: the kernel expands each literal to its characters and compares the
pairs character by character, so a 119-entry inventory paid ~7,000 string
comparisons per witness — 60 to 150 seconds of Tier 1 per inventory module,
about 690 seconds of build CPU across the thirteen (test-performance audit,
v0.34.47).

The representation here keeps every statement and every proof kernel-checked
while moving the kernel's work onto `Nat`, which it compares with GMP in one
step.  A string is stored as **one packed key**: its Unicode scalar values as
base-`2^21` digits (`packedStringRadix`), most significant first, behind a
leading `1` that fixes the digit count.  Each inventory entry carries the
key together with a proof that the key is *well formed* —
`isWellFormedPacked`: it packs exactly the digits it unpacks to, and every
digit is a valid scalar value — discharged per entry by `decide +kernel`
(~14 ms each).  The string itself is derived, `stringOfPacked`, never stored.

Distinctness then follows from distinctness of the keys
(`nodup_map_stringOfPacked`): two well-formed keys spelling the same string
unpack to the same digits (`String.ofList` and `Char.ofNat` are injective on
valid scalar values), and a well-formed key is the packing of its own digits,
so the keys are equal.  The one remaining kernel computation per inventory is
`nodupNat` over the key list — ~7,000 GMP comparisons instead of ~7,000
character walks.

Two shapes were measured and rejected on the way here.  A `List Nat` of
scalar values per entry is exact but the compiler is superlinear in a
literal of ~15,000 list cells, so each inventory paid ~12 s to *compile*
instead; and deciding well-formedness of every key in one list-level fold
re-evaluates the per-key work through `brecOn` and costs ~13 s where the
per-entry proof fields cost ~3 s.  Neither the key nor the proof field is
visible at an inventory's entries: each `<inventory>! "description" name
category` line is unchanged, and the macro packs both strings.
-/

namespace SeLe4n

/-- One digit per Unicode scalar value: every scalar value is below
    `0x110000 < 2^21`, so digits never carry into each other. -/
def packedStringRadix : Nat := 0x200000

/-- Fold the digits onto an accumulator, most significant first. -/
def packCodesAux (acc : Nat) : List Nat → Nat
  | [] => acc
  | c :: cs => packCodesAux (acc * packedStringRadix + c) cs

/-- Pack scalar values into one `Nat`: base-`2^21` digits behind a leading `1`. -/
def packCodes (codes : List Nat) : Nat := packCodesAux 1 codes

/-- The packed key of a string: its scalar values, packed. -/
def packString (s : String) : Nat := packCodes (s.toList.map Char.toNat)

/-- Peel digits off `k` onto `acc` until only the leading `1` is left.  The
    fuel is structural so the kernel can run it; a key is far larger than its
    own digit count, so passing the key as its own fuel never runs short. -/
def unpackCodesAux : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | fuel + 1, k, acc =>
    if k ≤ 1 then acc
    else unpackCodesAux fuel (k / packedStringRadix) (k % packedStringRadix :: acc)

/-- The digits of a packed key, most significant first. -/
def unpackCodes (k : Nat) : List Nat := unpackCodesAux k k []

/-- Decode scalar values into the string they spell. -/
def stringOfCodes (codes : List Nat) : String :=
  String.ofList (codes.map Char.ofNat)

/-- The string a packed key spells. -/
def stringOfPacked (k : Nat) : String := stringOfCodes (unpackCodes k)

/-- `Nat.isValidChar`, as the `Bool` the kernel evaluates. -/
def isValidCode (c : Nat) : Bool := c < 0xd800 || (0xdfff < c && c < 0x110000)

def allValidCodes : List Nat → Bool
  | [] => true
  | c :: cs => isValidCode c && allValidCodes cs

/-- A key is well formed when it packs exactly the digits it unpacks to and
    every digit is a valid scalar value.  Decided per entry by `decide +kernel`. -/
def isWellFormedPacked (k : Nat) : Bool :=
  packCodes (unpackCodes k) == k && allValidCodes (unpackCodes k)

/-- Pairwise distinctness of `Nat`s as a `Bool` fold: `List.elem` against the
    tail, so the kernel's work is one GMP comparison per pair. -/
def nodupNat : List Nat → Bool
  | [] => true
  | k :: ks => !ks.elem k && nodupNat ks

/-- The packed key of `s` as a raw numeral, for an inventory macro to splice
    into an entry.  Raw (`nat_lit`) rather than `OfNat`-wrapped: the kernel
    then compares the literal itself. -/
def packedStringLit (s : String) : Lean.TSyntax `num :=
  Lean.Syntax.mkNumLit (toString (packString s))

/-! ## Soundness -/

theorem isValidCode_iff {c : Nat} : isValidCode c = true ↔ c.isValidChar := by
  simp [isValidCode, Nat.isValidChar]

theorem allValidCodes_iff :
    ∀ {cs : List Nat}, allValidCodes cs = true ↔ ∀ c ∈ cs, c.isValidChar
  | [] => by simp [allValidCodes]
  | c :: cs => by
    simp only [allValidCodes, Bool.and_eq_true, isValidCode_iff, allValidCodes_iff,
      List.mem_cons, forall_eq_or_imp]

theorem isWellFormedPacked_iff {k : Nat} :
    isWellFormedPacked k = true ↔
      packCodes (unpackCodes k) = k ∧ ∀ c ∈ unpackCodes k, c.isValidChar := by
  simp only [isWellFormedPacked, Bool.and_eq_true, beq_iff_eq, allValidCodes_iff]

theorem nodupNat_sound : ∀ {l : List Nat}, nodupNat l = true → l.Nodup
  | [], _ => List.nodup_nil
  | k :: ks, h => by
    simp only [nodupNat, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact List.nodup_cons.mpr ⟨fun hm => by simp_all, nodupNat_sound h.2⟩

theorem Char.toNat_ofNat_of_isValidChar {n : Nat} (h : n.isValidChar) :
    (Char.ofNat n).toNat = n := by
  unfold Char.ofNat
  rw [dif_pos h]
  rfl

theorem Char.ofNat_injective_of_isValidChar {n m : Nat}
    (hn : n.isValidChar) (hm : m.isValidChar) (h : Char.ofNat n = Char.ofNat m) :
    n = m := by
  have := congrArg Char.toNat h
  rwa [Char.toNat_ofNat_of_isValidChar hn, Char.toNat_ofNat_of_isValidChar hm] at this

theorem map_ofNat_injective_of_isValidChar :
    ∀ {cs ds : List Nat}, (∀ c ∈ cs, c.isValidChar) → (∀ d ∈ ds, d.isValidChar) →
      cs.map Char.ofNat = ds.map Char.ofNat → cs = ds
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | c :: cs, d :: ds, hcs, hds, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hc := Char.ofNat_injective_of_isValidChar (hcs c (List.mem_cons_self ..))
      (hds d (List.mem_cons_self ..)) h.1
    have hrest := map_ofNat_injective_of_isValidChar
      (fun x hx => hcs x (List.mem_cons_of_mem _ hx))
      (fun x hx => hds x (List.mem_cons_of_mem _ hx)) h.2
    rw [hc, hrest]

theorem stringOfCodes_injective_of_isValidChar {cs ds : List Nat}
    (hcs : ∀ c ∈ cs, c.isValidChar) (hds : ∀ d ∈ ds, d.isValidChar)
    (h : stringOfCodes cs = stringOfCodes ds) : cs = ds :=
  map_ofNat_injective_of_isValidChar hcs hds (String.ofList_injective h)

/-- Well-formed keys that spell the same string are the same key. -/
theorem stringOfPacked_injective {k₁ k₂ : Nat}
    (h₁ : isWellFormedPacked k₁ = true) (h₂ : isWellFormedPacked k₂ = true)
    (h : stringOfPacked k₁ = stringOfPacked k₂) : k₁ = k₂ := by
  obtain ⟨hp₁, hv₁⟩ := isWellFormedPacked_iff.mp h₁
  obtain ⟨hp₂, hv₂⟩ := isWellFormedPacked_iff.mp h₂
  have hu : unpackCodes k₁ = unpackCodes k₂ :=
    stringOfCodes_injective_of_isValidChar hv₁ hv₂ h
  rw [← hp₁, ← hp₂, hu]

/-- The inventory payoff: entries whose well-formed keys are pairwise distinct
    spell pairwise distinct strings.  `hWf` is each entry's own proof field;
    `hKeys` is the one kernel computation, `decide +kernel` over the keys. -/
theorem nodup_map_stringOfPacked {α : Type} (key : α → Nat) {l : List α}
    (hWf : ∀ a ∈ l, isWellFormedPacked (key a) = true)
    (hKeys : nodupNat (l.map key) = true) :
    (l.map (fun a => stringOfPacked (key a))).Nodup := by
  have hNodup := nodupNat_sound hKeys
  rw [List.Nodup, List.pairwise_map] at hNodup ⊢
  rw [List.pairwise_iff_getElem] at hNodup ⊢
  intro i j hi hj hij heq
  exact hNodup i j hi hj hij
    (stringOfPacked_injective (hWf _ (List.getElem_mem hi)) (hWf _ (List.getElem_mem hj)) heq)

end SeLe4n
