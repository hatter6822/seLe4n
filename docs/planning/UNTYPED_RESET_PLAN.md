# Untyped reset as seL4's (WS-ZA ZA5.4, parts 11–19)

Decided by Adam on the ZA5.4 thread (card, 2026-10-21): the untyped reset reaches
zero allocations the way seL4 does it, not by rewriting today's whole-store reset
as proven loops.  This plan schedules that change; the ZA5.4 row of
[`ZERO_ALLOCATION_SYSCALL_PLAN.md`](ZERO_ALLOCATION_SYSCALL_PLAN.md) owns the
row's status and readings.

## 1. What seL4 does (read from `src/object/untyped.c`, `objecttype.c`, `cnode.c`)

- **The free pointer is in the capability** (`capFreeIndex`).  A retype carves at
  the invoked capability's free index and advances it.
- **A reset is a retype whose capability has no derivation children.**
  `decodeUntypedInvocation` calls `ensureNoChildren(slot)`; when it succeeds the
  free index is 0 and `invokeUntyped_Retype` runs `resetUntypedCap` first.
  Otherwise the carve starts at the capability's own free index.  The refusal
  for space is `seL4_NotEnoughMemory`.
- **An untyped capability is copied only while it has no children**
  (`deriveCap`: `ensureNoChildren`, else a null capability), and the insert sets
  the source's free index to full (`setUntypedCapAsFull` in `cteInsert`), so only
  the copy carves from then on.
- **The object goes when its last capability goes.** `finaliseCap` runs when
  `isFinalCapability` holds: no MDB neighbour names the same object.

## 2. What the tree does today

- The free pointer is the object's (`UntypedObject.watermark`), so a carve through
  a copy of the capability is not a derivation child of the copy it did not use.
  Fixed by part 13 (`v0.36.124`): the free index is the capability's
  (`Capability.freeIndex`) and derivation follows seL4's rule.
  For that reason the reset is dispatched by object id and walks the carved
  subtree (`untypedCarvedSubtree`).  It also scans the whole store for
  references (`carvedSubtreeUnreferenced`), then erases each carved object
  (`retireCarvedObjects`).  This costs 151 cells.
- No delete erases an object: `retireCarvedObject` is the store's one erase.
- The carve adds the derivation edge `src → dst` (`cdtAddChild … .retype`).  The
  slot's first-child word answers "has children" in one read (`linkHasChild`,
  equal to the tree's answer under `LinksAgree`).
- A carve makes only four kinds of object: frames, untypeds, address-space roots
  and page tables (`CarveRequest`).
- Two references to a carved object live outside slots, and the whole-store scan
  exists to find them.  A thread's address space is an object id
  (`TCB.vspaceRoot`, `Model/Object/Types.lean:1182`).  A blocked sender's parked
  message's type can hold resolved capabilities (`IpcMessage.caps`, read by
  `objectNamesListed`, `Architecture/PageTeardown.lean:656`).  No executable path
  writes any: a blocked sender parks addresses and the receiver resolves them at
  the rendezvous (`senderFrameMessage` sets `caps := #[]`,
  `IPC/DualQueue/SenderMessage.lean:136`).  The reply paths' `caps.size >
  maxExtraCaps` checks are therefore dead.
  Fixed by part 11 (`v0.36.121`: `IpcMessage` has no capability field, the dead
  checks and the parked-message arm are deleted) and part 12 (`v0.36.122`: a
  thread's address space is a capability in a TCB slot, which
  `objectNamesListed` reads).
- `setThreadSpace` (`Lifecycle/Operations/SetSpace.lean`) receives the space
  capabilities, checks them and discards them.  It records no derivation edge, so
  revoking the VSpace capability a thread was given does not reach the thread.
  Derivation nodes are CNode slots only (`SlotRef`, `Model/Object/Types.lean:375`).
  Fixed by part 12 (`v0.36.122`): the roots are two capability slots in the TCB,
  derivation nodes, and `copyThreadSpaces` copies the given capabilities into
  them with their derivation edges; `setThreadSpace` is deleted.

- Same-object capabilities are not kept together in the tree.  A delete re-adds
  the deleted slot's children at the front of its parent's child list
  (`spliceEdges`, `linkSpliceNode`, `CDT/SlotLinks.lean:801`), and a move re-adds the
  moved node at the front (`moveEdges`, `linkMoveNode`, `:867`); seL4 keeps the
  list position.  A slot with no parent has no sibling links (`LinksAgree`,
  `Model/Object/DerivationLinks.lean:594`), and deleting it orphans its children.
  Boot puts two capabilities to one object in two unlinked slots (the root CNode
  slot and the root thread's CSpace slot, likewise the VSpace;
  `Platform/RPi5/Deployment.lean:257-293`).  So "neither parent nor child names
  the object" is not finality: after a delete, two copies of one object can be
  siblings.
- Kernel objects (TCBs, CNodes, endpoints, notifications, replies, scheduling
  contexts) are made only by retyping an existing object in place
  (`lifecycleRetypeDirectWithCleanup`, `Lifecycle/Operations/RetypeWrappers.lean`),
  which needs the retype right on that object.  Boot grants that right only on
  untypeds, so no kernel object can be made at runtime, and the in-place path
  has no check that nothing still names its target.  Its error-code oracle
  (cleanup before the authority check) is fixed at `v0.36.123`.

## 3. Design

- **D1 Finality is read from the tree in seL4's MDB order** (decided by Adam,
  2026-10-21: "tree in seL4 order").  The tree's preorder is made equal to seL4's
  MDB list: an insert puts the new child first under its source (as today, which
  is right after the source in preorder), a delete puts its children where it
  was among its siblings, and a move keeps the slot's place.  Slots with no
  parent form one sibling chain, so every slot has its `prev` and `next` words.
  Boot derives its duplicate capabilities from the root CNode's slots, as seL4's
  `create_initial_thread` does.  The invariant (`sameObjectContiguous`) is
  seL4's `mdb_chunked`: the slots naming one object are one contiguous preorder
  run.  A capability is final when its preorder neighbours do not name its
  object (seL4's `isFinalCapability`), read from its parent, first-child,
  `prev` and `next` words.  No reference count and no new word is kept.
- **D2 Retire on final delete, for every kind.**  A delete or revoke that
  destroys a final capability finalises its object as seL4's `finaliseCap` does,
  then retires it (`retireCarvedObject`).  For memory kinds that is the unmap and
  detach the teardown already does.  For kernel kinds it is seL4's: an endpoint
  cancels all its IPC, a notification unbinds and cancels its waiters, a thread
  is suspended and unbound and its two space slots deleted, a reply is cancelled,
  a scheduling context unbound, and a CNode's slots deleted by seL4's zombie
  loop.  Once every kind is carved (D6), an object no capability names is
  memory the untyped can reuse, so nothing may outlive its last capability.
- **D3 The free index moves into the capability.**  `Capability` gains a
  `freeIndex` word, meaningful only for an untyped target, and
  `UntypedObject.watermark` is deleted.  The carve reads and advances the invoked
  slot's word in place.  Copy and mint of an untyped capability are refused while
  it has children (`.revocationRequired`); otherwise the source's word is set to
  full.  The untyped memory invariants (`untypedWatermarkInvariant`, the
  children-bounds and non-overlap invariants) are restated over capabilities, as
  seL4's `untyped_inc`.
- **D5 Every reference to a carved object is a slot.**  As in seL4 (the TCB's
  `tcbVTable` slot), a thread holds its address space as a capability derived
  from the one it was given, in a slot of its own.  So a bound root keeps a
  descendant capability, and its last capability goes only with the thread's.
  A parked message holds capability addresses, looked up at the rendezvous as
  seL4's `lookupExtraCaps` does, never resolved capabilities.  The part that
  closes this deletes the TCB-field and parked-message arms of
  `objectNamesListed`.
- **D6 Every object kind is carved from an untyped** (decided by Adam,
  2026-10-21: "carve every kind").  `CarveRequest` covers every kernel object
  kind, sized and aligned as seL4's `Untyped_Retype`, and a carved TCB starts
  with empty space slots.  The in-place retype (`lifecycleRetypeDirectWithCleanup`
  and its wrappers, the CSpace-address family `lifecycleRetypeWithCleanup` and
  `Internal.lifecycleRetypeObject`, their theorems and the `.lifecycleRetype`
  syscall arm) is deleted.
- **D4 Reset is `ensureNoChildren` and a rewind.**  Syscall 37 is dispatched on
  the invoked slot.  It refuses while that slot has a derivation child, and
  otherwise writes 0 to its free index: O(1), with no scan and no erase.  Like
  seL4, the retype also resets when its capability has no children.  The
  subtree walk, the whole-store reference scan, `UntypedObject.children` (if
  nothing else consumes it) and every theorem that only they pin are deleted in
  that same part.

## 4. Schedule

| Part | Work |
|---|---|
| 11 | **No message holds a capability.**  `IpcMessage` loses its capability array and grant bit; capability transfer takes the array resolved at the rendezvous (`ipcUnwrapCaps`), the reply paths' dead extra-capability refusal and the unused gated resolvers are deleted, and the reset's reference scan loses its parked-message arm.  Landed at `v0.36.121`, structurally rather than as an invariant |
| 12 | **A thread's spaces are slots** (D5; consumes 11).  A TCB holds two capability slots, its CSpace and VSpace roots, as seL4's `tcbCTable` and `tcbVTable`.  They are derivation nodes: `SlotRef` names a TCB slot as it names a CNode slot, over the same cell and link words.  `setThreadSpace` copies the given capabilities into them, recording the derivation edges.  `TCB.cspaceRoot` and `TCB.vspaceRoot` become reads of those slots, proven equal, and a thread's teardown deletes them.  The binding, context-switch and IPC-buffer theorems are restated.  Landed at `v0.36.122`, in the steps below; the copy masks the source's rights by the root's, and every user CNode invocation now refuses unless it invokes a CNode (`cnodeInvoked`), as seL4's `decodeCNodeInvocation`, so `CNode_Delete` on a thread capability cannot empty the thread's root slots |
| 13 | **Free index in the capability** (D3; consumes 12).  The untyped invariants are restated over capabilities, and the boot's untyped capabilities are given their indices; copying an untyped capability with children is refused, and otherwise the source is set full.  Retype pins unchanged.  Landed at `v0.36.124`: the rule covers copy, CDT-tracked mint and IPC transfer (a refused transfer stops, as seL4's `transferCaps`); the reset entry refuses an invoked slot with a child and rewinds its index; the free-index write holds `stateLevelLock` as the link words do; boot refuses one untyped named by two capabilities.  `untyped-reset` reads 161 (151 before), the rewind copied behind the whole-store reset's late refusals, until part 19.  Boot is not yet proven to establish `untypedMemoryInvariant` (`docs/REGISTERED_DEBT.md` §C) |
| 14 | **Every kind is carved** (D6; consumes 13).  The carve makes every kernel kind at the invoked capability's free index; the in-place retype, its syscall arm and its theorems are deleted.  Every pin unchanged.  Landed at `v0.36.125`: the carve covers every kind with seL4's sizes, rounding the free index up to the object's boundary as seL4's `alignUp(freeRef, objectSize)`, the in-place retype and its arm are deleted (number 8 reserved, mirrored in Rust), and the §C authority-order row is closed.  The per-kind exerciser scenarios are part 18's: a carve repeats only after its object is finalised |
| 15 | **The tree in seL4 order** (D1's structure; consumes 14).  Delete and move keep the slot's position, roots form a sibling chain, and boot derives its duplicate capabilities from the root CNode's slots.  `LinksAgree` and the splice and move theorems are restated.  Every pin unchanged |
| 16 | **Finality** (D1's invariant; consumes 15).  `sameObjectContiguous` is proven preserved by every slot write (copy, mint, move, transfer, set-space, delete, revoke, carve) and established by boot.  `capIsFinal` reads the four link words and is proven equal to "no other slot names the object" under it |
| 17 | **Retire memory kinds on final delete** (D2; consumes 16).  The delete and revoke teardowns retire a frame, page table, address-space root or untyped whose final capability they destroy.  Exerciser: `frame-delete` and `page-table-delete-*` stay at 0 |
| 18 | **Finalise kernel kinds on final delete** (D2; consumes 17).  seL4's `finaliseCap` for every kernel kind, then the retire; a CNode by the zombie loop.  The delete theorems are restated.  Exerciser: carve then delete each kernel kind, pinned at the object's own cells, then reset reads its pin |
| 19 | **The seL4 reset** (D4; consumes 18).  The reset and its theorems are restated (the untyped's capability holds index 0, and nothing carved remains below its index), and the deleted code is removed.  Exerciser: `untyped-reset` reads 0 at first call and steady state |

### Part 12 in steps (each compiles; proofs land with or before the code they cover)

The TCB holds its slots in fixed-size fields (`spaceCells`, two cells; `spaceLinks`, their link words, the same layout as `CNode.cells` and its links).  Slot readers and writers dispatch on the object kind, the `.cnode` arm being today's function, so every CNode theorem is reused.  This adds no store lookup on the context switch or the IPC-buffer fill.  A companion CNode per TCB was rejected: it needs a second object per retype and a second erase, it adds a lookup to every root read, and seL4's TCB slots are inside the TCB.

1. **12.1 Roots are slot reads.**  `TCB.cspaceRoot` / `vspaceRoot` become definitions reading cells 0 and 1, with a setter `TCB.withSpaceCaps` and its simp lemmas; boot and `objectOfKernelType .tcb` fill the cells.  Behaviour is unchanged.
2. **12.2 Object-slot dispatch.**  The slot-link readers and writers, `linksOnlyWrite`, `objectsAgreeOffDerivationLinks`, `cdtCompleteness`, `cspaceLookupSound`, `replyCapPointsToValidReply` and `capabilityBadgesWellFormed` read slots through the dispatch; the information-flow projection of a TCB hides its link words; the runtime slot checks cover TCB slots.  No TCB slot is in the tree yet.
3. **12.3 Delete, revoke and finality reach TCB slots** (`cspaceDeleteSlotCore`, the finalising delete, `revokeFirstChildLoop`, `cnodeSlotsUnreferenced`, `objectNamesListed`'s TCB arm), with the delete and revoke preservation restated.
4. **12.4 Teardown.**  A thread's cleanup splices its two slots out (`detachTcbSlots`), as a CNode's cleanup splices its slots.
5. **12.5 The copying set-space, proven.**  As seL4: the old slot content is deleted, then the copy is inserted with the edge from its source slot; the capability, link and information-flow bundles are proven.
6. **12.6 Live.**  The set-space resolver returns the source slots and the dispatcher runs 12.5; the old `setThreadSpace` is deleted.

