# WS-UC — Untyped-backed object cells

> **Workstream**: WS-UC (a carved object's cells in its untyped's memory).
> **Status**: **ACTIVE** — registered at `v0.37.1`; UC1 landed at `v0.37.2`,
> UC5 at `v0.37.18`.
> **Baseline**: the tree at `v0.37.0` (WS-ZA closed, ZA6.37). Every
> `file:line` below was re-read against it.
> **Closes**: the `docs/REGISTERED_DEBT.md` row "Only the retype checks the
> kernel heap's capacity…", re-homed here at `v0.37.0` and closed by UC9.
> **Rows**: UC1–UC10, numbered in the order they are implemented. Each row
> consumes only lower-numbered rows, and a row that changes a transition
> carries the proofs that cover it. No two rows run in parallel.
> **Decisions**: D1–D7 (§3). D1–D6: **default taken; owner card open** on each.
> D7: **decided by the owner** (`v0.37.18`).

## 1. The problem

A carve today puts every cell it builds in the kernel's Lean heap, one
64 MiB arena behind one leaf lock (`rust/sele4n-hal/src/lean_heap.rs:931-1013`).
The arena halts when it is full (`heap_halt`, `:1183`). So the retype checks
the heap's free bytes before it writes anything (`CarveRequest.heapAdmitted`,
`SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean:1314`), measured
against stated per-kind constants (`:1255-1306`). Those constants are not
derived from the compiled layouts, and the check is not seL4's.

seL4 charges a retype to the untyped it carves from. `decodeUntypedInvocation`
(`src/object/untyped.c`) aligns the free index to the object size and answers
`seL4_NotEnoughMemory` when `(untypedFreeBytes >> objectSize) < nodeWindow`.
The kernel object then lives in that memory. This workstream does the same: a
carved object's cells live in its untyped's region, a carve costs its region's
bytes by construction, and the heap check retires.

**What stays a Rust fact.** No Lean theorem can say where a cell lives. The
model keeps proving the carve's result. Containment (the cells are in the
range, and none outlives it) is enforced by the region allocator's live counts,
read wherever bytes are handed out again. UC7 records this limit in
`docs/CLAIM_EVIDENCE_INDEX.md`.

## 2. Facts the rows rest on

Each fact is stated once, here, and the rows cite it by its letter.

- **F1. The carve is pure and runs in one step.** It runs inside
  `modifyGetKernelState` (`SeLe4n/Kernel/SyscallDispatchEntry.lean:861-869`),
  after the entry reads the heap's free bytes (`:852`). So no `IO` bracket can
  name the untyped to the allocator. A context word around the whole step
  would also route table, resize and index cells into the region. The carve
  therefore runs its builder through a pure extern that sets **this core's**
  allocation context only around the object's own construction. It is
  per-core because a secondary core's bring-up probe allocates outside the
  entry lock (`lean_heap.rs:70-79`).
- **F2. What a carve builds.** `untypedRetypeObject` (`ScrubAndUntyped.lean:1359`)
  does three things. It builds the object (`CarveRequest.objectImpl`,
  `:1130-1143`), where the kinds built from constants pass through
  `KernelObject.unshareFresh` (`SeLe4n/Model/Object/Unshare.lean:254`). It
  stores the object one table at a time (`storeFresh`,
  `SeLe4n/Model/State.lean:2500-2507`). And it records the child in the untyped
  (`UntypedObject.allocate`, `SeLe4n/Model/Object/Types.lean:4210`). The
  compiled object-table insert already places a supplied entry cell
  (`RHTable.insertCell` and `insertAbsentCell`,
  `SeLe4n/Kernel/RobinHood/Core.lean:805,1006`).
- **F3. The pins.** `scripts/qemu_exerciser_lib.sh:241-243` pins each carve's
  cell count (the `v0.37.0` counts are §5's baseline column). They cover the object's own cells, its
  entries in the object, index-set and type tables, its index row, and its
  child record (`:233-236`). At `v0.37.0` no VSpace-root or child-untyped
  carve was measured (`carved_kind`, `rust/sele4n-hal/src/smp_exercisers.rs`,
  named both, but no scenario carved either). UC1 adds both, a byte pin beside
  each cell pin, and the derived check that every kind the decode accepts is
  carved and deleted.
- **F4. Ranges are owned by address.** A carve through a capability with no
  derivation child starts at 0 (`retypeFreeIndex`, `ScrubAndUntyped.lean:223`).
  That carve is refused while the untyped records a child (`:232-234`). A
  retired child untyped's records are spliced up to its recorder
  (`retireUnrecord`, `SeLe4n/Kernel/Capability/FinalRetire.lean:752`). So an
  ancestor's reset is refused while any descendant lives. These rules hold beside the sole-carver
  and non-overlap invariants (`SeLe4n/Kernel/Lifecycle/Invariant.lean:113-130`).
- **F5. How a cell can outlive its range.** None of these ways is an
  allocation, so the zero-allocation gate cannot see them:
  - *Reuse.* Lean's reset/reuse puts a constructor into a dead cell of the same
    size. `objIdListDrop`
    (`SeLe4n/Kernel/Lifecycle/Operations/CarvedObjectErase.lean:84-86`)
    re-conses the kept index cells.
  - *Sharing.* `CapTarget.copyOver` returns `src` itself for a `.cnodeSlot`
    target or a destination that is not one-field (`Types.lean:1396-1406`). A
    carved CNode slot's kept record holds the boot reply object's shared target
    (the move-slot CNode carve, WS-ZA ZA5.4 part 26).
  - *Relocation.* The compiled insert's displacement arm builds
    `some { e with dist := e.dist + 1 }` (`insertCellLoop`, `Core.lean:741-761`),
    and a resize rebuilds every entry.
  - *Snapshot.* `freeze` shares object cells through `objects.toList`
    (`SeLe4n/Model/FrozenState.lean:672`), and no live entry runs it.
- **F6. User pages are zeroed at their carve.** The carve zeroes a frame
  (`PhysicalWrite.zeroPage` → `apply_physical_write`,
  `rust/sele4n-hal/src/user_translation.rs:349-365`). A RAM frame maps only as
  Normal write-back (`frameMappingAdmissible`, `SeLe4n/Kernel/API.lean:2694-2699`).
  A device untyped backs no kernel kind (`ScrubAndUntyped.lean:320`).

## 3. Owner decisions

D1–D6 are each **default taken; owner card open**. A different answer on the
card changes only the rows that cite that decision. D7 is decided by the owner.

- **D1. Where the records of page kinds live.** The record cells of a frame,
  page table, VSpace root and child untyped cannot live in their own range,
  because that range is user memory, a walked table or future carves. *Default:*
  a **metadata page per untyped**. It is carved from the untyped's free index on
  the first page-kind carve that needs it, and it is modelled in Lean, so
  `canAllocate` charges it. Device untypeds have no RAM to hold one, so their
  frame records come from a **fixed boot pool**, with a Lean-visible count.
- **D2. A reset or a zero over live cells.** *Default:* the rows make this
  **unreachable by construction**: own cells only (UC4), no table structure in
  a window (UC2, UC3), and only the object's own construction inside the
  context (UC7). The allocator **halts only as a backstop**. Two things support
  this: the generated-C scan (UC4) and the lifetime evidence (UC10). No
  Lean-visible quiescence word is added.
- **D3.** Retire `objectIndex`, `objectIndexSet` and `lifecycle.objectTypes` to
  erased ghosts (UC2). *Default:* accept the proof cost.
- **D4.** *Default:* accept the boot cost and keep `maxObjects` at 65536
  (`State.lean:2352`). The object table and the ASID table are pre-sized at
  boot (UC3). The allocator keeps one map byte per 512 B granule of the RAM
  the untypeds cover (UC5, D7). The map is reserved from physical RAM at boot,
  as seL4 reserves its boot-time structures, and never from the kernel heap:
  it takes the top pages of each RAM extension the boot maps, and the
  extension's untyped covers the rest (`Platform.Boot.RegionMapReservation`).
  An extension of `S` bytes reserves the fewest whole pages `R` with
  `513 · R ≥ S`, about 2 MiB of RAM per GiB, which leaves the untypeds
  `S - R`. On QEMU `virt` with 1 GiB, the 768 MiB extension reserves
  384 pages (1.5 MiB) at `[0x7FE8_0000, 0x8000_0000)`. On a 16 GiB Raspberry
  Pi 5 the two extensions (0.75 GiB and 15 GiB) reserve 384 and 7666 pages,
  about 31.4 MiB of RAM. The heap pays nothing (boot census: CHANGELOG
  `v0.37.18`).
- **D5.** *Default:* object sizes are ABI-visible and larger than seL4's.
  `objectTypeAllocSize` (`ScrubAndUntyped.lean:42-54`) is the **one owning
  definition**. `rust/sele4n-abi` and the spec take the sizes from it (UC6).
- **D6.** *Default:* close the heap-capacity row whole, on the exerciser
  reading (UC9). That includes its second half, "every other heap growth"
  (a mapping's table entry, a derivation record), which stays a gate reading
  and not a theorem.
- **D7. Where a region address finds its range.** *Decided by the owner*
  (`v0.37.18`): **one map byte per 512 B granule, and a range is at least
  512 B.** Kernel kinds are smaller than a page, and carves bumped at their
  own alignment put ranges of different sizes in one page. So one byte per
  page could not name an address's range. The other ways found the range
  through bytes inside the range or its padding, which a user can control: a
  stale frame, a notification word, a thread's saved registers. Those bytes
  could forge a header for the D2 backstop. The map is kept outside every
  range, and nothing in a range's bytes decides which range an address is in.
  The alternatives were a page minimum on every range, or a per-page byte with
  a per-page start bitmap. Either would change only `rust/sele4n-hal/src/region/map.rs`.

## 4. Rows

Each row lists every cell it decides and where that cell goes, and it names the
boundary cell of each rule it adds. Acceptance is stated as exerciser readings
(`heap-allocations-per-syscall`). Unless a row says otherwise, **every reading
the row does not name stays as it was**. The pins have one site,
`scripts/qemu_exerciser_lib.sh`'s `carve_cells`, and each row that moves a pin
rewrites it there.

### UC1 — Measure each carve — **LANDED `v0.37.2`**

- **Work.**
  - Make each carve print the bytes of each cell it allocates, by size, next to
    its cell count. This is a reading only; behaviour does not change. *Done:*
    the heap keeps each core's latest 64 allocation sizes by allocation number
    (`kernel_allocation_sizes_on`, `rust/sele4n-hal/src/lean_heap.rs`), and
    every reading line ends `bytes=<n> sizes=<size>x<count>,…`. The gate holds
    the sizes to the counted cells and the bytes to the sizes, and refuses an
    unrecorded window.
  - Add the two kinds no scenario carves (F3), `untyped-retype-vspace-root` and
    `untyped-retype-untyped`, each with its own cell pin, and the delete of each
    one's capability (`vspace-root-delete`, `child-untyped-delete`).
  - Add a byte pin beside each cell pin in `carve_cells`.
  - **The kind coverage is derived.** The gate takes the kinds an untyped
    retype can name from the retype's own decode (`decodeUntypedRetypeArgs`,
    run by `scripts/retype_object_kinds.lean`). It holds each kind to a pinned
    carve scenario and to a pinned delete of that carve's capability: the first
    delete of the carve's slot before its steady-state carve succeeds again at
    the same id. A failed or empty derivation fails the gate. Tested by
    breaking the relation (a dropped delete line, a delete of another slot, a
    steady carve at another id): each fails.
  - **Fixed on the way: a VSpace root's final delete read 1810 heap cells.**
    `retireCarvedObjectImpl` ran the specification's body for a root, whose
    every field read one shared state. So each table it erased was copied whole,
    and every shifted entry and index cell was rebuilt. It now erases one table
    at a time in place and then releases the ASID (`withAsidReleased`). Its ASID
    round writes over an ASID-round spare, as a page round writes over the page
    spare (`tlbShootdownBroadcastAsid`, `asidReleaseRoundImpl`, and the
    `shootdownAsid*Spare` fields seeded at boot). Proofs:
    `retireCarvedObject_eq_impl`, `tlbShootdownBroadcastAsid_eq`,
    `asidReleaseRound_eq_impl`. The delete now reads 0.
- **Cells.** Measures every cell of every carve. Breaks each pin down into four
  groups: object cells, the bookkeeping (the index row, the index set and the
  type table), the object-table entry, and the child record (§5).
- **Measured the design's two inferences.** Both hold:
  - an endpoint's 11 cells are 2 object cells plus 9 store cells;
  - the ghosts of UC2 remove 5 cells (120 bytes) from every carve.
- **Acceptance.**
  - The 8 existing pins are unchanged.
  - The two new kinds read their new pins: VSpace root 14 cells and
    376 bytes, child untyped 12 cells and 304 bytes.
  - `vspace-root-delete` and `child-untyped-delete` read 0, at first call and
    in steady state.
  - Every kind the decode accepts has a pinned carve and a pinned delete.
  - §5's table is filled in from this reading.
  - Every other reading stays 0.

### UC2 — The bookkeeping tables become ghosts (D3) — **LANDED `v0.37.15`**

- **Done.** The three fields are `SeLe4n.Erased` ghosts (`objectIndexGhost`,
  `objectIndexSetGhost`, `LifecycleMetadata.objectTypesGhost`, and their frozen
  forms), read only through `noncomputable` readers.  Their agreement with the
  object table is `SystemState.bookkeepingAgrees`, carried by the boot's
  `IntermediateState` and the kernel invariant bundle's 22nd component, which
  every kernel entry keeps (`MappingStage.bookkeeping`;
  `syscallDispatchEntryState_preserves_bookkeepingAgrees` and its twins for the
  other entries).  The reply-receive's capability-transfer store guard, true on
  every state once an in-place store asks only for the key's kind, is deleted
  and the dispatch equivalences re-proven without it.  The capacity
  check reads `objects.size`; the PIP fuel, the information-flow index
  (sorted, `sortObjIds`; executable form `projectObjectIndexByTable`, proven
  equal), the SGI and admission walks, `storeIsFresh` and the store-locality
  kind checks read the object table, each walk proven order-independent.
  `storeFresh` writes the object and ASID tables only; `withObjectIndexed`,
  `withObjectIndexSet`, `withObjectType`, `objIdListDrop` and the retire's
  per-table erases are deleted.  The boundary is tested
  (`runObjectStoreCapacityBoundaryChecks`).  Every carve pin fell by 5 cells /
  120 bytes, every other reading 0 (CHANGELOG `v0.37.15`).
- **Work.**
  - Retype `objectIndex`, `objectIndexSet` and `lifecycle.objectTypes` as
    `SeLe4n.Erased` (`SeLe4n/Model/Erased.lean`), as WS-ZA did for the run
    queue's abstract queue.
  - Prove that each one agrees with `objects` on every reachable state. This
    is the largest proof cost in the workstream.
- **The set of compiled reads to re-point is derived, not listed.** It is
  exactly what the compiler refuses once the fields are erased, because
  `Erased.out` is `noncomputable`. Examples at `v0.37.0`:
  - the capacity check `objectIndex.length ≥ maxObjects`
    (`ScrubAndUntyped.lean:296-297`), which becomes `objects.size`;
  - the PIP-chain fuel `objectIndex.length` (e.g.
    `SeLe4n/Kernel/IPC/Operations/Donation.lean:1322`);
  - the `filterMap` walks (e.g. `SeLe4n/Kernel/SchedContext/Operations.lean:418`);
  - `storeIsFresh` (`State.lean:2469`) and the type reads (`:2464`).
- **Each re-pointed walk proves its result does not depend on order.** The
  object table's iteration order follows its slot layout (`State.lean:1270-1284`).
- **Cells.**
  - The index cons cell, and the `some` and `RHEntry` cells of the index-set and
    type tables, are no longer built: carves, retires and `objIdListDrop`'s
    re-cons stop making them.
  - `storeFresh` (`State.lean:2500-2507`) keeps the object table and the ASID
    table only.
- **Boundary.** The capacity check's boundary cell is the carve at
  `objects.size = maxObjects − 1`, which succeeds. The carve after it is refused
  with `objectStoreCapacityExceeded` before any write.
- **Acceptance.**
  - Each carve's pin falls by the 5 ghost cells (120 bytes) UC1 measured
    (endpoint 11 → 6, 368 → 248 bytes).
  - Every other reading stays 0.

### UC3 — Pre-size the object and ASID tables at boot (D4) — **LANDED `v0.37.16`**

- **Done.** The boot's empty state (`SystemState.bootEmpty ()`, through
  `mkEmptyIntermediateState ()`), which the boot's builder starts from, builds
  `objects` and `asidTable` at `bootTableCapacity` (2^17), where the boot calls
  it and never as a module constant (`never_extract`); the default state keeps
  16-slot tables, so no closed state holds a boot-sized table and the boot's
  heap cost is the installed state's two tables.  On such a table
  holding at most `maxObjects` objects (or `maxAsidValue` ASIDs) `insert` is
  `insertNoResize` (`SystemState.objects_insert_eq_insertNoResize`,
  `SystemState.asidTable_insert_eq_insertNoResize`, over
  `RHTable.insert_eq_insertNoResize_of_load`).  The capacity fact
  (`SystemState.tablesPresized`) is `bookkeepingAgrees.presized`, so it rides in
  the bundle's 22nd component as UC2's agreement does and every kernel entry
  keeps it: `ghostsKept` and `BookkeepingKept` say neither table shrinks, every
  table write carries a capacity lemma, and the cross-core legs prove it per leg
  (`*_objects_capacity_le`).  Bundle corollaries
  `proofLayerInvariantBundle.objects_insert_eq_insertNoResize` and
  `.asidTable_insert_eq_insertNoResize`; the carve's
  `retypeFromUntyped_insert_eq_insertNoResize`; the heap model's resize term
  reads 0 there (`rhInsertResizeHeapBytes_objects_eq_zero`).  No `@[csimp]`
  drops the insert's resize branch: the equation needs the load hypothesis,
  which the compiled insert cannot see.  The empty table's slot array is built
  in one allocation (`@[csimp] RHTable.empty_eq_emptyImpl`).
  The boundary is tested (`runObjectStoreCapacityBoundaryChecks`).  Readings
  and the boot's heap cost: CHANGELOG `v0.37.16`.
- **Work.**
  - Boot builds `objects` and `asidTable` at capacity 2^17. That holds
    `maxObjects` objects and `maxAsidValue` ASIDs
    (`SeLe4n/Kernel/Architecture/AsidManager.lean:75`, 65536) below the 75%
    resize load (`RHTable.insert`, `Core.lean:999-1002`).
  - Theorem: on a state whose `objects.size < maxObjects`, `insert` equals
    `insertNoResize`, and likewise for the ASID table. So a live insert never
    resizes.
- **Cells.** The tables' slot arrays and their resizes are heap cells built at
  boot only, never inside a carve.
- **Boundary.** The insert at size 65535 into capacity 131072 does not resize
  (4·65535 < 3·131072). UC2's capacity check refuses the next carve.
- **Acceptance.**
  - Each kind's first-call reading equals its steady-state reading.
  - The pins are unchanged.
  - Every other reading stays 0.

### UC4 — A carve owns its cells, and no pass moves them — **LANDED `v0.37.17`**

- **Done.** `CapTarget.copyOver` writes any source into the destination's
  own target cell whatever either names (`CapTarget.over`): every target
  constructor carries one word, a CNode slot's pair packed into one
  (`CapTarget.cnodeSlotWord`, `SeLe4n.pairWords`); `copyOver_eq` still holds.  `Capability.ofFields`, the
  record the no-spare build path of `insertCellWith` stores, builds its target
  afresh (`CapTarget.fresh`, `fresh_eq`, `Capability.ofFields_eq`), so a minted
  reply capability no longer holds the reply object's own target cell.  In
  `insertCellLoop` the displacement arm moves the displaced entry
  (`RHEntry.bumpDist`) and the present-key arm writes the slot's own entry
  (`RHEntry.withValue`); `insertCellLoop_eq` still holds.  A scan of the
  generated C found three more reuse sites that filled one cell with
  another's fields, each now out of line and joined by `@[csimp]`: the queue
  unlink's neighbour writes (`queueUnlinkPredecessor_eq_impl`,
  `queueUnlinkSuccessor_eq_impl`) and the slot lookup's result
  (`cspaceLookupSlot_eq_impl`).  The scan is not kept (owner decision, see
  the scanner item below).  Each fix is a fast form proven equal to its
  specification; that it owns its cell is how it is written, checked for
  `copyOver` by cell address in `ModelIntegritySuite` and for a CNode's
  carve-to-retire by the window below.  The
  heap counts frees per core (`kernel_frees_on`), and the owned-CNode window
  (carve, a capability copied into the carved CNode and out of it into a root
  slot, the carved slot's delete and the carved capability's delete, the
  escaped copy living on past the retire) allocates and frees 23 cells, the cnode/2 pin,
  in both runs.  Measured, no pin rises: UC1 attributed no cell to sharing,
  and the exercised carves already built every cell they hold (the shared
  target was reachable only on the no-spare build path and the `.cnodeSlot`
  arm, which no pinned scenario takes).  Readings: CHANGELOG `v0.37.17`.
- **Work.**
  - `CapTarget.copyOver` builds its own cell in its last two arms, the
    `.cnodeSlot` arm and the destination that is not one-field (F5). Proof:
    `copyOver_eq` still holds.
  - The boot reply's shared target gets its own cell.
  - The compiled insert's displacement arm and `bumpDist` move the displaced
    cell; they do not rebuild it (F5, `insertCellLoop`). Proof:
    `insertCellLoop_eq` still holds.
  - A committed Tier 1 scanner over the generated C of the store, Robin Hood,
    retire and capability-copy code. It flags any reset/reuse that puts a value
    built for one key or object into a cell taken from another. The ZA6.31
    scanner is not in the tree; it lives only in that audit's evidence. This
    row commits one, and tests it by breaking the relation (CLAUDE.md).
    *Dropped (owner decision):* a scan that traces fields only within one
    function cannot decide a field that comes from a parameter or a call
    result, and refusing those fails 181 real sites (in-place updates
    through a helper, the in-place copy itself, list loops) that no source
    change inside one function resolves.  The claim rests on the proofs of
    the fixes and on the owned-CNode window.
- **Cells.** Every target cell, spare record and entry cell a carve builds is
  that carve's own, and no later operation moves it into another object.
- **Boundary.** The arm that changes is the non-one-field destination over a
  `.cnodeSlot` source. A one-field destination already owns its cell.
- **Acceptance.**
  - The cnode/2 pin, and any other pin that held a shared cell, rises by the
    cells UC1 attributed to sharing.
  - A new reading: carve a CNode, copy a capability out of it, then delete and
    revoke it. The cells it frees equal its pin. *Met:* the copy out
    outlives the retire, and the window frees 23, the cnode/2 pin.
  - The scanner reports 0 hits on the tree. *Dropped with the scanner.*
  - Every other reading stays 0.

### UC5 — The region allocator, inert (Rust) — **LANDED `v0.37.18`**

- **Done.** `rust/sele4n-hal/src/region/`. The map (`region/map.rs`) keeps one
  byte per 512 B granule (D7). It is 0 when the granule is in no recorded
  range, and otherwise the log2 size of the range that holds it. So a range's
  base is the address with its low bits cleared, and no lookup reads region
  memory.
  - **The reservation.** The map's storage is reserved from physical RAM, not
    taken from the kernel heap (D4). The Lean boot owns the layout
    (`SeLe4n/Platform/Boot/RegionMapReservation.lean`): the map takes the top
    of each RAM extension, and both deployments build their untypeds from
    `untypedExtentOf`, so no untyped covers the map. Proofs show the map of
    the covered RAM fits (`regionMap_fits_reserve`), the untyped and the map
    tile the extension (`untypedSizeOf_tiles`), every accepted RPi5 extension
    fits (`rpi5BootRamExtensions_fit`), and no RPi5 untyped meets a map
    (`rpi5RootTaskUntypeds_clear_of_regionMaps`). The QEMU layout is decided
    (`qemuVirtRegionMap_layout`). `extendBootRamMap` hands the HAL each
    extension's covered part and map base (`ffi_reserve_region_map`) after
    mapping it. The HAL checks the layout (`reservation_layout`): unaligned,
    unmapped or overlapping input halts the boot, and a map is never shrunk.
    It then zeroes the map and registers it (`register_reserved_map`). Every
    thread-memory decode takes `thread_ram_covered`, which refuses a
    reservation's pages, so the map is kernel-only.
  - **The header.** A range's header holds its log2 size, an atomic live
    count, a bump cursor, a cell-start bitmap and a live bitmap, one bit per
    8 bytes each. It is `24 + size / 32` bytes (`header_bytes`), 40 B for a
    512 B range.
  - **Free and size.** A free clears the cell's live bit with one atomic
    `fetch_and`, which refuses a double free, and decrements the count. It
    takes no lock, and the bytes are not reused. A cell's size runs to the
    next cell start, or to the cursor.
  - **Classification.** The heap's free, size and usable-size entries classify
    by address: inside the arena they go to the heap, outside it to the
    region. That covers `lean_free_small`, `lean_small_mem_size`, the big
    path's `kernel_free` / `kernel_usable_size`, and so `allocated_bytes`.
  - **The context.** The per-core allocation context is a word per core.
    `lean_heap`'s two allocation entries consult it. It is set only through
    `enter_context`, whose guard masks interrupts while it is held, and
    nothing calls `enter_context` yet.
  - **The backstop.** `Region::begin_range` and `admit_page_zero` (called by
    `apply_physical_write` before a zero) find every recorded range meeting
    the bytes through the map. They halt on a live count above 0, and
    otherwise unrecord those ranges whole.
  - **Tests.** Host tests in `region/tests.rs` cover each boundary, a planted
    leaked cell, and the backstop query on a page of mixed sizes whose padding
    holds forged headers. They also cover the QEMU reservation layout and each
    refusal, a lookup over every granule of the covered RAM with the map in
    the reservation, and reservations excluded from thread RAM and from each
    other. The heap's own test covers the routing. `ak9_platform_suite` checks
    that every board's untypeds stop at their region maps.
  - **Readings.** Every QEMU reading is unchanged, and the boot census is
    unchanged. Readings and the census: CHANGELOG `v0.37.18`.
- **Work** (`rust/sele4n-hal`):
  - a per-core allocation context;
  - a range header inside each range: the range's size, an atomic live count,
    a bump cursor and a cell-start bitmap;
  - a per-granule log2-size byte (D7), allocated at boot, that maps an address
    to its range;
  - free, size and usable-size classified by address on both the small path
    and the big path (`lean_heap.rs:1190-1218`, `lean_runtime/mod.rs:340-352`,
    `lean_runtime/mem.rs:40-48`). The header has no spare bits
    (`m_cs_sz = 0`), so this is the only record of a region cell's size;
  - **the backstop of D2**: initialising a range header, or zeroing a page
    (`apply_physical_write`), over bytes whose range has a live count above 0
    halts.
- A free decrements its range's live count without taking the heap lock, and
  it never reuses the bytes. They return at the reset, as seL4's
  `resetUntypedCap` returns them.
- **Cells.** None yet: nothing sets the context.
- **Boundary.**
  - A live count of 1 at a zero halts; a live count of 0 zeroes.
  - A bump that would pass the range's end halts. A cell that ends exactly at
    the end is served. UC6's sizes make the halt unreachable.
- **Acceptance.**
  - Host tests cover each boundary, including a planted leaked cell.
  - `test_rust.sh` and `test_aarch64_cross_build.sh` pass.
  - Every QEMU reading is unchanged.

### UC6 — Honest sizes, owned once (D5)

- **Work.**
  - Set `objectTypeAllocSize`, `CarveRequest.sizeW`
    (`SeLe4n/Kernel/Lifecycle/Operations/RetypePerform.lean:429-435`) and
    `cnodeSlotBits` to each kind's footprint plus UC5's range header. The
    footprint is the byte pin after UC4. Sizes are rounded up to a power of
    two, and to at least 512 B, the region map's granule (D7). So
    `alignedCarveIndex` and the alignment lemmas keep their form, and the
    CNode's size still scales with its radix. UC5's header for a range of
    `S` bytes is `24 + S / 32` bytes (`region::header_bytes`).
  - Re-run the proofs.
  - `rust/sele4n-abi` (`CNODE_SLOT_BITS`, `MIN_SCHED_CONTEXT_SIZE_BITS` and a new
    per-kind size table, `src/args/lifecycle.rs`) is checked against the Lean
    definition by a boundary probe that runs the compiled Lean
    (`SeLe4nBoundaryProbes`). It is not a second hand-written list.
  - The spec cites the definition.
  - The exerciser checks a relation: each carve's measured bytes are at most
    the size the carve was charged.
- **The check is seL4's.** `canAllocate` (`Types.lean:4202-4203`) against the
  free index is `decodeUntypedInvocation`'s `seL4_NotEnoughMemory` check. With
  honest sizes it is the bound.
- **Cells.** None move.
- **Boundary.** An untyped whose free bytes past the aligned index equal the
  size succeeds. One alignment unit fewer is refused with
  `untypedRegionExhausted`. This is a new negative case in
  `tests/NegativeStateSuite.lean`.
- **Acceptance.**
  - The pins are unchanged.
  - The new negative case refuses.
  - Every other reading stays 0.

### UC7 — Carve the object kinds into their range

- **Work.**
  - An `@[extern "sele4n_build_carved_object", never_extract] def` takes the
    range (`ut.regionBase + carveIndex`, the size) and the carve's scalars,
    not a built object (F1). Its Lean body is the model's `req.object …`, so no
    proof changes.
  - The Rust side sets this core's context, calls an `@[export]`ed builder
    (today's `objectImpl` / `unshareImpl`), and clears the context.
  - The same window builds the object-table entry cell, which is placed by
    `RHTable.insertCell` (F2), and the child record (the cons cell and its
    `UntypedChild`). The child record's lifetime is the object's: the retire
    removes it, and it is spliced only up (F4), into a range that still
    contains it.
  - Record in `docs/CLAIM_EVIDENCE_INDEX.md` that containment is a Rust fact
    (§1).
- **Kinds.** TCB, endpoint, notification, CNode, reply and scheduling context.
- **Cells.** Every cell of these carves lives in the carve's range, including a
  TCB's space-slot spares and a CNode's slot records. The object-table slot
  array stays on the heap (UC3).
- **Boundary.** The first cell is the range header's successor. The last cell
  ends at or before the range's end, and UC6's size makes that so.
- **Acceptance.**
  - **Every carve of these kinds reads 0 from the kernel heap.**
  - The new `region-cells` reading equals each kind's pin.
  - Every other reading stays 0.

### UC8 — Page kinds and device untypeds (D1)

- **Work.** The records of a frame, page table, VSpace root and child untyped
  are built in their untyped's metadata page, and so are their entry cells,
  their child records and a root's ASID-table entry. The metadata page is
  carved from the untyped's free index, and the Lean model holds its slot
  count. A device untyped's frame records come from the boot pool.
- **Cells.** A root's empty mapping table, as measured by UC1, goes in the
  metadata page. A mapping's later growth is the D6 half.
- **Boundary.**
  - The carve that fills the metadata page's last slot succeeds. The next one
    carves a new metadata page, or, with no room for one, is refused with
    `untypedRegionExhausted`.
  - The boot pool's last record succeeds. The next one is refused with
    `untypedRegionExhausted`.
  - Like seL4's frames, a metadata page returns only at the reset.
- **Acceptance.**
  - Frame, page-table, VSpace-root and child-untyped carves, from both RAM and
    device untypeds, read 0 from the kernel heap.
  - Their region readings equal their pins.
  - Every other reading stays 0.

### UC9 — Retire the heap capacity (D6)

- **Work.** Delete the heap check, its theorems and its readings in one cut.
  The set is **derived**: every declaration whose code view names
  `heapAdmitted`, `heapBytes` or `kernelHeapFreeBytes`, plus every by-name
  consumer (Tier 1 censuses, Tier 3 anchors, the exerciser's expected set).
  At `v0.37.0` that set reaches:
  - `retypeHeapReserveBytes` … `CarveRequest.heapAdmitted` and the guard
    (`ScrubAndUntyped.lean:1255-1315,1362`);
  - the `heapAdmittedW*` family and the `_heapRefused` theorems
    (`RetypePerform.lean:145-243,481-493,541-642`);
  - `SeLe4n/Kernel/RefusalCarryingInvocation.lean:947,1571-1580`;
  - `MachineState.kernelHeapFreeBytes` and `kernelHeapArenaBytes`
    (`SeLe4n/Machine.lean:906,1082`), and `withKernelHeapFreeBytes`
    (`SeLe4n/Kernel/Architecture/IpcBufferRead.lean:531-533`);
  - the entry's read and its body marker
    (`SyscallDispatchEntry.lean:852,940,952`);
  - `ffiKernelHeapFreeBytes` (`SeLe4n/Platform/FFI.lean:3657`) and
    `ffi_kernel_heap_free_bytes` (`rust/sele4n-hal/src/ffi.rs:1927`);
  - the ceiling hook (`lean_heap.rs:1138-1171`) and `heap_refused_retype`
    (`smp_exercisers.rs:5766`);
  - `tests/NegativeStateSuite.lean:2219-2272`;
  - the Tier 3 anchors (`scripts/test_tier3_invariant_surface.sh:3913-3924`
    and their neighbours).
- `heapAdmitted` is **retired, not replaced**: UC6's `canAllocate` is the bound.
- **Cells.** None.
- **Boundary.** Retire the `untyped-retype-heap-refused` scenario.  The
  `untyped-retype-region-exhausted` scenario, which WS-SX SX1 (`v0.37.20`)
  added, already measures a carve the region cannot hold; UC6 keeps it.
- **Acceptance.**
  - Every pin holds.
  - The new scenario refuses.
  - Every other reading stays 0.
  - The heap-capacity row closes whole (D6).

### UC10 — Lifetime evidence per kind (D2)

- **Work.** One QEMU scenario per kind:
  1. Carve.
  2. Delete and revoke. Every cell is freed, and the range's live count
     reads 0.
  3. Reset the untyped.
  4. Carve a frame over the same bytes. The zero passes.
- Add a leaked-cell hook (an exerciser-only build) that keeps one cell alive
  past its delete.
- **Cells.** None.
- **Boundary.** With the hook, the leaked cell's range reads live count 1, and
  the zero halts (UC5's backstop).
- **Acceptance.**
  - Each kind reads live count 0 after its delete, and its reset and zero
    pass.
  - The hook run halts at the zero with the range named.
  - Every other reading stays 0.
- **Closure duty (the workstream's last row).**
  - **Full documentation sweep against WS-UC's final tree:** the spec, every
    GitBook chapter on untyped memory, retype and the heap, README metrics,
    `docs/DEVELOPMENT.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, the
    `docs/REGISTERED_DEBT.md` index row, and
    `docs/agent_guide/WORKSTREAM_CONTEXT.md`, whose WS-UC section moves to
    `docs/dev_history/planning/CLOSED_WORKSTREAM_CONTEXT.md`.
  - **Refresh every not-yet-started plan** under `docs/planning/` against
    WS-UC's final tree: file:line citations, names, rows the final tree makes
    obsolete or newly needs, and the decisions it affects.
  - If the refresh is too large for UC10, it is the very next PR, landed
    before any next-row code.

## 5. The per-kind byte table (filled by UC1)

Measured at `v0.37.2` on QEMU `virt`, against a fresh archive. Two untraced runs
agree, and a traced run's counts equal them. Each group is cells / bytes,
attributed by disassembling the traced image.

| Kind | Cells | Bytes | Object | Ghost tables | Entry | Child record |
|------|------:|------:|-------:|-------------:|------:|-------------:|
| endpoint/0 | 11 | 368 | 2 / 144 | 5 / 120 | 2 / 48 | 2 / 56 |
| notification/0 | 11 | 360 | 2 / 136 | 5 / 120 | 2 / 48 | 2 / 56 |
| reply/0 | 15 | 376 | 6 / 152 | 5 / 120 | 2 / 48 | 2 / 56 |
| tcb/0 | 24 | 2160 | 15 / 1936 | 5 / 120 | 2 / 48 | 2 / 56 |
| sched-context/7 | 13 | 560 | 4 / 336 | 5 / 120 | 2 / 48 | 2 / 56 |
| cnode/2 | 28 | 1248 | 19 / 1024 | 5 / 120 | 2 / 48 | 2 / 56 |
| frame/0 | 11 | 272 | 2 / 48 | 5 / 120 | 2 / 48 | 2 / 56 |
| page-table/0 | 13 | 352 | 4 / 128 | 5 / 120 | 2 / 48 | 2 / 56 |
| vspace-root/0 | 106 | 3688 | 95 / 3416 | 5 / 120 | 2 / 48 + 2 / 48 ASID entry | 2 / 56 |
| untyped/12 | 12 | 304 | 3 / 80 | 5 / 120 | 2 / 48 | 2 / 56 |

- **VSpace root** (since `v0.37.10`): the object group holds the root's own
  mapping and epoch tables and their spare cells, built at the carve
  (`KernelObject.unshareFresh`) so the root's first map writes them in place
  instead of copying a shared empty table; the heap admission counts them
  (`carvedVSpaceRootHeapBytes`).  Before, the object group was 3 / 104 and the
  pin 14 / 376.
- **Ghost tables** (UC2): the index row's cons cell (24 B), and a `some` cell
  (16 B) and an `RHEntry` (32 B) in each of the index-set and type tables
  (`withObjectIndexed`, `withObjectIndexSet`, `withObjectType`).  Gone since
  `v0.37.15` (UC2): every pin is 5 / 120 below this table's.
- **Entry**: the object table's `some` cell and `RHEntry` (`withObjectInserted`).
  A VSpace root also has an entry of the same shape in the ASID table
  (`withAsidRegistered`).
- **Child record**: a 24 B cell and a 32 B cell built in the untyped's update
  (`storeUntypedWith`).
- **Object**: the kernel-object cell (16 B) and what the kind is built of. A
  VSpace root's empty mapping table costs no cell at its carve: it is a shared
  constant (F5; UC8 decides where its first cells go).

## 6. The seL4 behaviours this follows

| Behaviour | seL4 | Rows |
|-----------|------|------|
| The retype's size check | `decodeUntypedInvocation` (`src/object/untyped.c`): it aligns the free index to the object size, then answers `seL4_NotEnoughMemory` when `(untypedFreeBytes >> objectSize) < nodeWindow` | UC6, UC9 |
| The reset | `resetUntypedCap` (`src/object/untyped.c`): when `ensureNoChildren` succeeds, it clears the region and sets the free index to 0. Bytes freed earlier return only here | F4, UC5, UC8, UC10 |
| No user mapping covers untyped memory that holds objects | The retype carves only the free region (l4v's `pspace_no_overlap` and `valid_untyped`), and a non-device frame is cleared when it is retyped (`clearMemory`). So no frame capability names bytes that hold a live object | F6, UC5 (zero-page guard), UC10 |

## 7. Asides recorded at planning

- **The stale "never pruned" docstring.** It was fixed in this plan's own PR
  (`v0.37.1`). `SystemState.objectIndex`'s docstring (`State.lean:1287`) said
  the index is never pruned. The retire does prune it
  (`CarvedObjectErase.lean:60`; `eraseRetiredObject`, `FinalRetire.lean:698-701`).
  The docstring now says what the code does.
- **The two MAIR encodings of "non-cacheable" were fixed in this plan's own
  PR (`v0.37.1`).** No live path disagreed, but they gave two answers to one
  question.
  - The staged backend's `fromPagePermissions`
    (`SeLe4n/Kernel/Architecture/VSpaceARMv8.lean`) gave a non-cacheable page
    AttrIndx 2, which is Normal non-cacheable in `MAIR_VALUE`
    (`rust/sele4n-hal/src/mmu.rs:93-97`). The live `userPageAttributes`
    (`SeLe4n/Kernel/Architecture/HardwareTables.lean`) gave it AttrIndx 1,
    which is Device-nGnRnE.
  - Index 1 is seL4's: AArch64 `makeUser3rdLevel` picks `NORMAL` or
    `DEVICE_nGnRnE` from `vm_attributes_get_armPageCacheable`.
  - The disagreement was latent. `VSpaceARMv8` is outside the import closure of
    both shipped archives (only `Platform/Staged.lean` and
    `tests/WxDefenseSuite.lean` import it). Its descriptors went only to its own
    model's `pageTableMemory`. And the HAL's `page_descriptor_admissible`
    (`rust/sele4n-hal/src/user_translation.rs:195-215`) refuses every user page
    descriptor whose AttrIndx is neither 0 nor 1.
  - **The fix.** Both encoders now read one owner, `userPageAttrIndex`
    (`SeLe4n/Kernel/Architecture/PageTable.lean`).
    `fromPagePermissions_attrIndex` states that the staged backend carries it.
    `tests/WxDefenseSuite.lean` T09 checks that the two encoders agree on a
    cacheable page and on a non-cacheable one. No theorem or test had pinned
    index 2.
