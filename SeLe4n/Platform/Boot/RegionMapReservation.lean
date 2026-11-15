-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude

/-!
# Boot — the region map's reservation

The HAL's region allocator finds a carved object's range through a map kept
outside every range: one byte per 512-byte granule of the RAM untypeds cover
(WS-UC decision D7).  The boot reserves that map from physical RAM, as seL4
reserves its boot-time kernel structures.  The map takes the top of each RAM
extension the boot maps, and the extension's untyped covers the rest.  So no
untyped covers the map, and no capability can ever retype or map it.

This module is the one owner of the layout.  The untyped lists of both
deployments are built from `untypedExtentOf`, and the boot hands the HAL
`untypedExtentOf` and `regionMapBaseOf` of each extension
(`Platform.FFI.extendBootRamMap`), whose reservation the HAL then checks.
-/

namespace SeLe4n.Platform

/-- The bytes of RAM one map byte describes: the region allocator's granule
    and smallest range. -/
def regionMapGranuleBytes : Nat := 512

/-- The bytes reserved for the map at the top of an extension of `size` bytes:
    the fewest whole pages `R` with `513 · R ≥ size`.  Then the map of the
    `size - R` bytes the untyped covers, one byte per granule, fits in `R`
    (`regionMap_fits_reserve`). -/
def regionMapReserveBytes (size : Nat) : Nat :=
  SeLe4n.pageBytes *
    ((size + (regionMapGranuleBytes + 1) * SeLe4n.pageBytes - 1) /
      ((regionMapGranuleBytes + 1) * SeLe4n.pageBytes))

/-- The bytes of an extension of `size` bytes its untyped covers: everything
    below the map's reservation. -/
def untypedSizeOf (size : Nat) : Nat :=
  size - regionMapReserveBytes size

/-- The part of a RAM extension `(base, size)` its untyped covers. -/
def untypedExtentOf (e : Nat × Nat) : Nat × Nat :=
  (e.1, untypedSizeOf e.2)

/-- The first byte of an extension's map reservation: the untyped's end. -/
def regionMapBaseOf (e : Nat × Nat) : Nat :=
  e.1 + untypedSizeOf e.2

/-- Whether an extension holds its reservation and at least one page of
    untyped memory beside it. -/
def regionMapFits (e : Nat × Nat) : Bool :=
  decide (regionMapReserveBytes e.2 + SeLe4n.pageBytes ≤ e.2)

/-- The untyped's part of an extension starts at the extension's base. -/
@[simp] theorem untypedExtentOf_fst (e : Nat × Nat) : (untypedExtentOf e).1 = e.1 := by
  unfold untypedExtentOf; rfl

/-- The untyped's part of an extension is `untypedSizeOf` of its size. -/
@[simp] theorem untypedExtentOf_snd (e : Nat × Nat) :
    (untypedExtentOf e).2 = untypedSizeOf e.2 := by
  unfold untypedExtentOf; rfl

/-- The untyped's part is no larger than the extension. -/
theorem untypedSizeOf_le (size : Nat) : untypedSizeOf size ≤ size := by
  unfold untypedSizeOf; omega

/-- The map of the untyped's part, one byte per granule, fits in the
    reservation. -/
theorem regionMap_fits_reserve (size : Nat) :
    untypedSizeOf size / regionMapGranuleBytes ≤ regionMapReserveBytes size := by
  unfold untypedSizeOf regionMapReserveBytes regionMapGranuleBytes SeLe4n.pageBytes
  omega

/-- The reservation is whole pages. -/
theorem regionMapReserveBytes_pages (size : Nat) :
    regionMapReserveBytes size % SeLe4n.pageBytes = 0 := by
  unfold regionMapReserveBytes
  exact Nat.mul_mod_right _ _

/-- An extension of at least two pages fits its reservation. -/
theorem regionMapFits_of_two_pages (e : Nat × Nat) (h : 2 * SeLe4n.pageBytes ≤ e.2) :
    regionMapFits e = true := by
  unfold regionMapFits regionMapReserveBytes regionMapGranuleBytes
  unfold SeLe4n.pageBytes at h ⊢
  exact decide_eq_true (by omega)

/-- The untyped's part and the reservation tile an extension that fits: the
    untyped is not empty and ends where the reservation begins, and the
    reservation ends where the extension does. -/
theorem untypedSizeOf_tiles (e : Nat × Nat) (h : regionMapFits e = true) :
    0 < untypedSizeOf e.2 ∧ regionMapBaseOf e = e.1 + untypedSizeOf e.2 ∧
      regionMapBaseOf e + regionMapReserveBytes e.2 = e.1 + e.2 := by
  unfold regionMapFits at h
  have h' := of_decide_eq_true h
  unfold regionMapBaseOf untypedSizeOf
  unfold SeLe4n.pageBytes at h'
  omega

/-- No address of an extension's reservation is in its untyped's part. -/
theorem regionMap_clear_of_untyped (e : Nat × Nat) (a : Nat)
    (h : regionMapBaseOf e ≤ a) : ¬ a < e.1 + untypedSizeOf e.2 := by
  unfold regionMapBaseOf at h
  omega

/-! ## The root server's reservation (WS-SX SX5.1, decision D13)

seL4's boot cuts one region out of free memory for the root task's own objects
before it makes a single untyped (`create_rootserver_objects`), so no untyped
covers them.  The boot here builds the root task's IPC buffer: the buffer frame
and the three tables (levels 1 to 3) that complete the walk to it from the root
task's top-level table.  Their four pages are cut from the last extension the
boot maps — seL4's `init_freemem` searches free memory from the top for the
rootserver region — directly below that extension's region map, so the
untyped of that extension ends where the reservation begins
(`untypedExtentsOf`). -/

/-- The pages of the root server's reservation: the IPC buffer frame and the
    three tables below the root task's top-level table that reach it. -/
def rootServerPages : Nat := 4

/-- The bytes of the root server's reservation. -/
def rootServerReserveBytes : Nat := rootServerPages * SeLe4n.pageBytes

/-- The first byte of the root server's reservation cut from extension `e`:
    directly below its region map. -/
def rootServerBaseOf (e : Nat × Nat) : Nat :=
  regionMapBaseOf e - rootServerReserveBytes

/-- The part of an extension its untyped covers when the extension also holds
    the root server's reservation, below it. -/
def untypedExtentBelowRootServerOf (e : Nat × Nat) : Nat × Nat :=
  (e.1, untypedSizeOf e.2 - rootServerReserveBytes)

/-- **The untyped parts of the extensions the boot maps**, in order: each
    extension's part below its region map (`untypedExtentOf`), the last one's
    below the root server's reservation too (`untypedExtentBelowRootServerOf`).
    The untyped lists of every deployment are built from it, and the boot hands
    the HAL the same parts as the RAM each region map describes. -/
def untypedExtentsOf : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | e :: rest =>
    (if rest.isEmpty then untypedExtentBelowRootServerOf e else untypedExtentOf e) ::
      untypedExtentsOf rest

/-- The parts are one per extension. -/
@[simp] theorem untypedExtentsOf_length (l : List (Nat × Nat)) :
    (untypedExtentsOf l).length = l.length := by
  induction l with
  | nil => rfl
  | cons e rest ih => simp only [untypedExtentsOf, List.length_cons, ih]

/-- Each part starts at its extension's base and is no larger than the part
    below the region map alone. -/
theorem untypedExtentsOf_getElem (l : List (Nat × Nat)) (i : Nat)
    (h' : i < (untypedExtentsOf l).length) :
    (untypedExtentsOf l)[i].1 = (l[i]'(by simpa using h')).1 ∧
      (untypedExtentsOf l)[i].2 ≤ untypedSizeOf (l[i]'(by simpa using h')).2 := by
  induction l generalizing i with
  | nil => simp at h'
  | cons e rest ih =>
    cases i with
    | zero =>
      simp only [untypedExtentsOf, List.getElem_cons_zero]
      split
      · unfold untypedExtentBelowRootServerOf; exact ⟨rfl, Nat.sub_le _ _⟩
      · unfold untypedExtentOf; exact ⟨rfl, Nat.le_refl _⟩
    | succ i =>
      simp only [untypedExtentsOf, List.getElem_cons_succ]
      exact ih i _

/-- Whether an extension holds its region map, the root server's reservation
    below it and at least one page of untyped memory below that. -/
def rootServerFits (e : Nat × Nat) : Bool :=
  decide (regionMapReserveBytes e.2 + rootServerReserveBytes + SeLe4n.pageBytes ≤ e.2)

/-- The reservation, the region map and the untyped below them tile an
    extension that fits: the untyped is not empty and ends where the
    reservation begins, which ends where the map begins. -/
theorem rootServer_tiles (e : Nat × Nat) (h : rootServerFits e = true) :
    0 < (untypedExtentBelowRootServerOf e).2 ∧
      e.1 + (untypedExtentBelowRootServerOf e).2 = rootServerBaseOf e ∧
      rootServerBaseOf e + rootServerReserveBytes = regionMapBaseOf e ∧
      regionMapBaseOf e + regionMapReserveBytes e.2 = e.1 + e.2 := by
  unfold rootServerFits at h
  have h' := of_decide_eq_true h
  unfold untypedExtentBelowRootServerOf rootServerBaseOf regionMapBaseOf untypedSizeOf
    rootServerReserveBytes rootServerPages SeLe4n.pageBytes
  unfold rootServerReserveBytes rootServerPages SeLe4n.pageBytes at h'
  simp only
  omega

/-- The reservation is whole pages. -/
theorem rootServerReserveBytes_pages : rootServerReserveBytes % SeLe4n.pageBytes = 0 := by
  unfold rootServerReserveBytes; exact Nat.mul_mod_left _ _

end SeLe4n.Platform
