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

The last extension also holds the root server's four pages directly below its
map (WS-SX SX5.1, `rootServerBaseOf`): the frame the boot builds the root
task's IPC buffer in and its three page tables, as seL4's boot carves its
rootserver objects before handing the rest of memory out as untypeds.  That
extension's untyped stops below them (`untypedExtentBelowRootServerOf`).

This module is the one owner of the layout.  The untyped lists of every
deployment are built from `untypedExtentsOf`, and the boot hands the HAL those
parts and `regionMapBaseOf` of each extension
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

/-- **WS-SX SX5.1 (decisions D13, D14): the root server's reservation** — what
    the boot needs to build the root task's IPC buffer, as seL4's boot builds its
    initial thread's (`create_rootserver_objects`, `create_ipcbuf_frame_cap`,
    `create_initial_thread`).

    Four pages of RAM from `base`: the buffer frame first, then the tables of
    levels 1, 2 and 3 that complete the walk to it from the root task's
    top-level table, each at the page after the one before.  They are cut from
    the last RAM extension the boot maps, directly below its region map
    (`rootServerBaseOf`), and that extension's untyped stops below them
    (`untypedExtentsOf`), so no untyped covers them: the
    `rootServerPlaced` conjunct of `Boot.PlatformConfig.wellFormed` refuses a
    reservation that is not in one RAM region, clear of every untyped, of the
    kernel's reserved extent and devices, and of every region map.

    The boot gives the four objects the ids from `firstObjId` up and their
    capabilities the root CNode slots from `frameSlot` up: the frame's, mapped
    (seL4's `seL4_CapInitThreadIPCBuffer`), then the three tables'.  It derives
    the frame's capability into the thread's buffer slot (`Model.TCB.ipcBufferSlot`,
    seL4's `tcbBuffer`) and sets its buffer address (`tcbIPCBuffer`) to
    `bufferVAddr`. -/
structure RootServerReservation where
  /-- The root task: seL4's initial thread, the one thread given a buffer. -/
  thread : SeLe4n.ThreadId
  /-- The reservation's first byte, page aligned. -/
  base : SeLe4n.PAddr
  /-- The root task's IPC buffer address, page aligned in its user window. -/
  bufferVAddr : SeLe4n.VAddr
  /-- The first of the four object ids: the frame's, then the three tables'. -/
  firstObjId : SeLe4n.ObjId
  /-- The first of the four root CNode slots: the frame's, then the three
      tables'. -/
  frameSlot : SeLe4n.Slot
  /-- The RAM extensions the boot maps, whose region maps the reservation lies
      clear of. -/
  ramExtensions : List (Nat × Nat)

namespace RootServerReservation

/-- Page `i` of the reservation: the frame's at 0, the level-`i` table's at
    `i` for `i` from 1 to 3. -/
def pageAddr (r : RootServerReservation) (i : Nat) : SeLe4n.PAddr :=
  SeLe4n.PAddr.ofNat (r.base.toNat + i * SeLe4n.pageBytes)

/-- Object `i` of the reservation: the frame at 0, the level-`i` table at `i`. -/
def objId (r : RootServerReservation) (i : Nat) : SeLe4n.ObjId :=
  SeLe4n.ObjId.ofNat (r.firstObjId.toNat + i)

/-- The root CNode slot of object `i`'s capability. -/
def cnodeSlot (r : RootServerReservation) (i : Nat) : SeLe4n.Slot :=
  SeLe4n.Slot.ofNat (r.frameSlot.toNat + i)

/-- The reservation's four pages are distinct. -/
theorem pageAddr_injective (r : RootServerReservation) {i j : Nat}
    (h : (r.pageAddr i).toNat = (r.pageAddr j).toNat) : i = j := by
  simp only [pageAddr, SeLe4n.PAddr.ofNat, SeLe4n.PAddr.toNat, SeLe4n.pageBytes] at h
  omega

/-- The reservation's four object ids are distinct. -/
theorem objId_injective (r : RootServerReservation) {i j : Nat}
    (h : r.objId i = r.objId j) : i = j := by
  have := congrArg SeLe4n.ObjId.toNat h
  simp only [objId, SeLe4n.ObjId.ofNat, SeLe4n.ObjId.toNat] at this
  omega

/-- **A reservation with its memory forgotten** — its pages and the extensions
    they are cut from, which are read off a board's account like an untyped's
    extent (`Boot.PlatformConfig.withoutExtents`).  Its thread, buffer address,
    object ids and slots are kept. -/
def withoutMemory (r : RootServerReservation) : RootServerReservation :=
  { r with base := SeLe4n.PAddr.ofNat 0, ramExtensions := [] }

/-- The reservation's four root CNode slots are distinct. -/
theorem cnodeSlot_injective (r : RootServerReservation) {i j : Nat}
    (h : r.cnodeSlot i = r.cnodeSlot j) : i = j := by
  have : (r.cnodeSlot i).toNat = (r.cnodeSlot j).toNat := congrArg SeLe4n.Slot.toNat h
  change r.frameSlot.toNat + i = r.frameSlot.toNat + j at this
  omega

end RootServerReservation

/-- **The reservation a deployment cuts from the extensions its boot maps**:
    the root server's four pages directly below the last extension's region map
    (`rootServerBaseOf`), and the deployment's thread, buffer address, object
    ids and root CNode slots.  `none` when the boot maps no extension.  What a
    platform binding's `rootServerFor` returns, so the reservation's memory and
    the untypeds (`untypedExtentsOf`) are cut from one list. -/
def rootServerReservationOf (extensions : List (Nat × Nat)) (thread : SeLe4n.ThreadId)
    (bufferVAddr : SeLe4n.VAddr) (firstObjId : SeLe4n.ObjId) (frameSlot : SeLe4n.Slot) :
    Option RootServerReservation :=
  extensions.getLast?.map fun e =>
    { thread := thread, base := SeLe4n.PAddr.ofNat (rootServerBaseOf e),
      bufferVAddr := bufferVAddr, firstObjId := firstObjId, frameSlot := frameSlot,
      ramExtensions := extensions }

/-- The reservation cut from either of two extension lists of one length has
    the same thread, buffer address, ids and slots: with its memory forgotten
    the two are one. -/
theorem rootServerReservationOf_withoutMemory (l l' : List (Nat × Nat))
    (h : l.length = l'.length) (thread : SeLe4n.ThreadId) (bufferVAddr : SeLe4n.VAddr)
    (firstObjId : SeLe4n.ObjId) (frameSlot : SeLe4n.Slot) :
    (rootServerReservationOf l thread bufferVAddr firstObjId frameSlot).map
        RootServerReservation.withoutMemory =
      (rootServerReservationOf l' thread bufferVAddr firstObjId frameSlot).map
        RootServerReservation.withoutMemory := by
  unfold rootServerReservationOf
  cases l with
  | nil => cases l' with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a rest => cases l' with
    | nil => simp at h
    | cons b rest' =>
      rw [List.getLast?_eq_getLast (by simp), List.getLast?_eq_getLast (by simp)]
      simp only [Option.map_some, RootServerReservation.withoutMemory]

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

/-- Each part is its extension's part below the region map, the last one's
    below the root server's reservation too. -/
theorem untypedExtentsOf_getElem_eq (l : List (Nat × Nat)) (i : Nat) (h : i < l.length) :
    (untypedExtentsOf l)[i]'(by simpa using h) =
      if i + 1 = l.length then untypedExtentBelowRootServerOf l[i] else untypedExtentOf l[i] := by
  induction l generalizing i with
  | nil => simp at h
  | cons e rest ih =>
    cases i with
    | zero =>
      simp only [untypedExtentsOf, List.getElem_cons_zero, List.length_cons, Nat.zero_add,
        Nat.add_right_cancel_iff]
      cases rest <;> simp
    | succ i =>
      simp only [untypedExtentsOf, List.getElem_cons_succ, List.length_cons,
        Nat.add_right_cancel_iff]
      exact ih i (by simpa using h)

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
