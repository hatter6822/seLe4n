-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Machine

/-!
# Boot — memory-map coverage

The vocabulary in which a board's own account of its memory (a device tree's
`/memory` nodes, parsed to a `MachineConfig`) is compared against what a
platform binding declares: does the account *cover* a region, and does it
cover every RAM region a machine configuration declares?

Split out of `Platform/Boot.lean` (PR #892 review round 2) because the
question is asked in two places that must give one answer: the
DeviceTree → `PlatformConfig` bridge (`deviceTreeCoversMachineConfig`,
`Platform/Boot.lean`) validates the board against the variant the binding
will install, and the binding itself (`Platform/RPi5/Board.lean`,
`rpi5VariantFor`) selects that variant by the same predicate.  The bindings
are upstream of `Platform/Boot.lean`, so the predicate sits here, beneath
both, importing only the machine model.

Two readings of "covered", disjoined in `memoryRegionCovered`: one entry
spanning the whole region, or the union of same-kind entries covering it.
The union reading is a greedy walk (`coverFrom`) whose soundness theorem
(`memoryRegionCoveredByUnion_sound`) says `true` means every address of the
region is inside some same-kind entry — so a `true` never claims memory the
account did not report, in either reading.
-/

namespace SeLe4n.Platform.Boot

/-- **PR #892 review round 2**: the furthest end among the regions of kind
`kind` that contain `cursor`, if any region does.

Recursive over the list rather than a fold, so `coverStep_attained` — the
maximum is *attained* by some region, which is what the soundness argument
needs — is an induction on the list. -/
def coverStep (kind : SeLe4n.MemoryKind) (cursor : Nat) :
    List SeLe4n.MemoryRegion → Option Nat
  | [] => none
  | q :: rest =>
    let acc := coverStep kind cursor rest
    if q.kind == kind && q.base.toNat ≤ cursor && cursor < q.endAddr then
      some (match acc with
        | none => q.endAddr
        | some e => max e q.endAddr)
    else acc

/-- **PR #892 review round 2**: the greedy walk from `cursor` towards `target`
over the regions of one kind — each step jumps to the furthest end of a region
containing the cursor, so a step retires every region that contained it, and
`regions.length` steps are always enough.  `fuel` is that bound. -/
def coverFrom (regions : List SeLe4n.MemoryRegion) (kind : SeLe4n.MemoryKind)
    (target : Nat) : Nat → Nat → Bool
  | 0, cursor => decide (target ≤ cursor)
  | fuel + 1, cursor =>
    if target ≤ cursor then true
    else
      match coverStep kind cursor regions with
      | none => false
      | some next => coverFrom regions kind target fuel next

/-- **PR #892 review round 2**: is every address of `r` inside *some* region of
`r`'s kind in `regions` — the union, not any one entry?

A device tree may describe one aperture the binding declares as a single region
across several adjacent or overlapping `reg` entries, and `memoryRegionCovered`
required a single entry to span the whole aperture, so such a board was refused
(`boardDoesNotMatchBinding`) by a check whose own contract said it should be
accepted.  `memoryRegionCoveredByUnion_sound` is the statement that the walk
answers the right question: `true` means every address of `r` is in some
same-kind region. -/
def memoryRegionCoveredByUnion (regions : List SeLe4n.MemoryRegion)
    (r : SeLe4n.MemoryRegion) : Bool :=
  coverFrom regions r.kind r.endAddr regions.length r.base.toNat

/-- **WS-RR RR7.27**: does `regions` cover all of `r`?

Containment rather than equality: a device tree may split one aperture the
binding declares as a single region across several entries, or report a larger
one, and either is a board that *has* what the binding needs.  What it may not
do is omit it.

Two readings, disjoined (PR #892 review round 2): a single entry spanning the
whole aperture — the RR7.27 form, kept as the first disjunct so
`memoryRegionCovered_of_mem` and everything on it are untouched — or the
**union** of the same-kind entries covering it, which is what the RR7.27
docstring above promised and the `any` did not deliver. -/
def memoryRegionCovered (regions : List SeLe4n.MemoryRegion)
    (r : SeLe4n.MemoryRegion) : Bool :=
  (regions.any fun q =>
    q.kind == r.kind &&
    q.base.toNat ≤ r.base.toNat &&
    r.endAddr ≤ q.endAddr) ||
  memoryRegionCoveredByUnion regions r

/-- **WS-RR RR7.27**: a region is covered by a map that contains it verbatim —
the reflexivity the coverage check needs to be satisfiable at all. -/
theorem memoryRegionCovered_of_mem (regions : List SeLe4n.MemoryRegion)
    (r : SeLe4n.MemoryRegion) (h : r ∈ regions) :
    memoryRegionCovered regions r = true := by
  unfold memoryRegionCovered
  rw [Bool.or_eq_true]
  refine Or.inl ?_
  refine List.any_eq_true.mpr ⟨r, h, ?_⟩
  simp

/-- **PR #892 review round 2**: the maximum `coverStep` returns is attained by a
region of the right kind that contains the cursor — the witness every step of
the walk hands to the soundness argument. -/
theorem coverStep_attained (kind : SeLe4n.MemoryKind) (cursor : Nat) :
    ∀ (regions : List SeLe4n.MemoryRegion) (next : Nat),
      coverStep kind cursor regions = some next →
      ∃ q ∈ regions, (q.kind == kind) = true ∧ q.base.toNat ≤ cursor ∧
        cursor < q.endAddr ∧ q.endAddr = next
  | [], next, h => by simp [coverStep] at h
  | q :: rest, next, h => by
    unfold coverStep at h
    simp only at h
    split at h
    · rename_i hGuard
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hGuard
      obtain ⟨⟨hKind, hBase⟩, hLt⟩ := hGuard
      cases hAcc : coverStep kind cursor rest with
      | none =>
        rw [hAcc] at h
        simp only [Option.some.injEq] at h
        exact ⟨q, List.mem_cons_self .., hKind, hBase, hLt, h⟩
      | some e =>
        rw [hAcc] at h
        simp only [Option.some.injEq] at h
        by_cases hle : e ≤ q.endAddr
        · exact ⟨q, List.mem_cons_self .., hKind, hBase, hLt,
            by rw [← h]; exact (Nat.max_eq_right hle).symm⟩
        · obtain ⟨q', hq', hK', hB', hL', hE'⟩ := coverStep_attained kind cursor rest e hAcc
          refine ⟨q', List.mem_cons_of_mem _ hq', hK', hB', hL', ?_⟩
          rw [← h, hE']
          exact (Nat.max_eq_left (Nat.le_of_lt (Nat.lt_of_not_le hle))).symm
    · obtain ⟨q', hq', hK', hB', hL', hE'⟩ := coverStep_attained kind cursor rest next h
      exact ⟨q', List.mem_cons_of_mem _ hq', hK', hB', hL', hE'⟩

/-- **PR #892 review round 2**: the walk is sound — a `true` from `cursor`
means every address from `cursor` up to `target` lies in some region of the
kind walked.  Induction on the fuel: each step's witness (`coverStep_attained`)
covers `[cursor, next)`, and the rest is the walk from `next`. -/
theorem coverFrom_sound (regions : List SeLe4n.MemoryRegion) (kind : SeLe4n.MemoryKind)
    (target : Nat) :
    ∀ (fuel cursor : Nat), coverFrom regions kind target fuel cursor = true →
      ∀ a, cursor ≤ a → a < target →
        ∃ q ∈ regions, (q.kind == kind) = true ∧ q.base.toNat ≤ a ∧ a < q.endAddr
  | 0, cursor, h, a, hLo, hHi => by
    simp only [coverFrom, decide_eq_true_eq] at h
    omega
  | fuel + 1, cursor, h, a, hLo, hHi => by
    unfold coverFrom at h
    split at h
    · omega
    · split at h
      · cases h
      · rename_i next hStep
        obtain ⟨q, hq, hK, hB, hL, hE⟩ := coverStep_attained kind cursor regions next hStep
        by_cases hNext : a < next
        · exact ⟨q, hq, hK, Nat.le_trans hB hLo, hE ▸ hNext⟩
        · exact coverFrom_sound regions kind target fuel next h a (Nat.le_of_not_lt hNext) hHi

/-- **PR #892 review round 2**: the union reading answers the question the
docstring asks — every address of `r` is inside some same-kind region. -/
theorem memoryRegionCoveredByUnion_sound (regions : List SeLe4n.MemoryRegion)
    (r : SeLe4n.MemoryRegion) (h : memoryRegionCoveredByUnion regions r = true) :
    ∀ a, r.base.toNat ≤ a → a < r.endAddr →
      ∃ q ∈ regions, (q.kind == r.kind) = true ∧ q.base.toNat ≤ a ∧ a < q.endAddr :=
  coverFrom_sound regions r.kind r.endAddr regions.length r.base.toNat h

/-- **PR #892 review round 2**: and so does the disjunction — whichever reading
accepted `r`, every one of its addresses is in a same-kind region.  The
single-entry reading is the union reading's special case. -/
theorem memoryRegionCovered_sound (regions : List SeLe4n.MemoryRegion)
    (r : SeLe4n.MemoryRegion) (h : memoryRegionCovered regions r = true) :
    ∀ a, r.base.toNat ≤ a → a < r.endAddr →
      ∃ q ∈ regions, (q.kind == r.kind) = true ∧ q.base.toNat ≤ a ∧ a < q.endAddr := by
  intro a hLo hHi
  unfold memoryRegionCovered at h
  rw [Bool.or_eq_true] at h
  rcases h with hOne | hUnion
  · obtain ⟨q, hq, hCond⟩ := List.any_eq_true.mp hOne
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hCond
    obtain ⟨⟨hK, hB⟩, hE⟩ := hCond
    exact ⟨q, hq, hK, Nat.le_trans hB hLo, Nat.lt_of_lt_of_le hHi hE⟩
  · exact memoryRegionCoveredByUnion_sound regions r hUnion a hLo hHi

/-- **PR #892 review round 2 — the finding's own shape**: the RPi5's 4 GiB low
aperture reported as two adjacent `reg` entries is covered.  Decided, so the
walk is exercised on the numbers a bootloader produces rather than on a
symbolic pair. -/
theorem memoryRegionCovered_split_low_aperture :
    memoryRegionCovered
      [ { base := SeLe4n.PAddr.ofNat 0, size := 0x40000000, kind := .ram },
        { base := SeLe4n.PAddr.ofNat 0x40000000, size := 0xBC000000, kind := .ram } ]
      { base := SeLe4n.PAddr.ofNat 0, size := 0xFC000000, kind := .ram } = true := by
  decide

/-- **PR #892 review round 2 (the negative)**: a gap between the pieces is not
covered, however they are cut — the walk stops at the first address no entry
contains. -/
theorem memoryRegionCovered_gap_refused :
    memoryRegionCovered
      [ { base := SeLe4n.PAddr.ofNat 0, size := 0x40000000, kind := .ram },
        { base := SeLe4n.PAddr.ofNat 0x40200000, size := 0xBBE00000, kind := .ram } ]
      { base := SeLe4n.PAddr.ofNat 0, size := 0xFC000000, kind := .ram } = false := by
  decide

/-- **PR #892 review round 2**: does the board `board` describes have all the
RAM `mc` declares, at least as wide a physical address space?

Only the `.ram` regions of `mc` are compared, and that is not a narrowing — it
is what a board's account is *about*: a device tree's `/memory` nodes describe
DRAM, its peripherals are a separate surface checked separately
(`deviceTreeCoversMmioRegions`), and `.reserved` regions are the binding's own
statement about memory it will not touch.

Fail-closed by construction: anything the account does not mention is not
covered, so an empty or partial map covers nothing but an empty demand.  This
is the predicate both the bridge and the RPi5 binding's variant selection
decide by (`deviceTreeCoversMachineConfig_eq`, `rpi5VariantsCoveredBy`). -/
def machineConfigCovers (board mc : SeLe4n.MachineConfig) : Bool :=
  mc.physicalAddressWidth ≤ board.physicalAddressWidth &&
  (mc.memoryMap.filter (fun r => r.kind == SeLe4n.MemoryKind.ram)).all
    (memoryRegionCovered board.memoryMap)

/-- **PR #892 review round 2**: a configuration covers itself — the witness
that the predicate is not vacuously false, and the shape a board matching its
own binding produces. -/
theorem machineConfigCovers_self (mc : SeLe4n.MachineConfig) :
    machineConfigCovers mc mc = true := by
  unfold machineConfigCovers
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.le_refl, true_and]
  refine List.all_eq_true.mpr ?_
  intro r hr
  exact memoryRegionCovered_of_mem _ r (List.mem_filter.mp hr).1

/-- **PR #892 review round 2**: what a `true` means — the physical address
space is at least as wide, and every address of every RAM region `mc`
declares lies inside some RAM region the board reported.  This is the
direction the boot relies on: a configuration the account covers never
declares RAM the board does not have. -/
theorem machineConfigCovers_sound (board mc : SeLe4n.MachineConfig)
    (h : machineConfigCovers board mc = true) :
    mc.physicalAddressWidth ≤ board.physicalAddressWidth ∧
    ∀ r ∈ mc.memoryMap, r.kind = SeLe4n.MemoryKind.ram →
      ∀ a, r.base.toNat ≤ a → a < r.endAddr →
        ∃ q ∈ board.memoryMap, q.kind = SeLe4n.MemoryKind.ram ∧
          q.base.toNat ≤ a ∧ a < q.endAddr := by
  unfold machineConfigCovers at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hPa, hAll⟩ := h
  refine ⟨hPa, ?_⟩
  intro r hr hKind a hLo hHi
  have hMem : r ∈ mc.memoryMap.filter (fun r => r.kind == SeLe4n.MemoryKind.ram) :=
    List.mem_filter.mpr ⟨hr, by simp [hKind]⟩
  have hCov := List.all_eq_true.mp hAll r hMem
  obtain ⟨q, hq, hK, hB, hE⟩ := memoryRegionCovered_sound board.memoryMap r hCov a hLo hHi
  refine ⟨q, hq, ?_, hB, hE⟩
  rw [beq_iff_eq] at hK
  rw [hK, hKind]

end SeLe4n.Platform.Boot
