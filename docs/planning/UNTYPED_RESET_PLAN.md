# Untyped reset as seL4's (WS-ZA ZA5.4, parts 11–16)

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

## 3. Design

- **D1 Finality is read from the tree, as seL4 reads its MDB.**  Copies, mints
  and transfers derive from an existing capability, a delete splices its children
  into its parent, and a move keeps the slot's place.  So the capabilities that
  name one object form a connected subtree of the derivation tree.  One
  invariant states this (`sameObjectConnected`).  A capability is then final when
  neither its parent nor any of its children names its object; for every carved
  kind, the second half is one first-child read.  No reference count is kept.
- **D2 Retire on final delete.**  A delete or revoke that destroys a final
  capability to a carved object retires the object (`retireCarvedObject`, its
  existing guard and theorems), after the unmap and detach the teardown already
  does.  Objects not of a carved kind keep today's behaviour.  Their finalisation
  is registered debt owned by ZA6.
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
| 13 | **Finality** (consumes 12). `sameObjectConnected` is stated and proven preserved by every slot write (copy, mint, move, transfer, delete, revoke, carve); boot establishes it.  `capIsFinal` reads the parent and first-child words and is proven equal to "no other slot names the object" under the invariant |
| 14 | **Retire on final delete** (consumes 13).  The delete and revoke teardowns retire a carved object whose final capability they destroy (D2), and the delete theorems are restated.  Exerciser: `frame-delete` and `page-table-delete-*` stay at 0 |
| 15 | **Free index in the capability** (consumes 14).  D3, with the untyped invariants restated over capabilities and the boot's untyped capabilities given their indices.  Retype pins unchanged |
| 16 | **The seL4 reset** (consumes 15).  D4: the reset and its theorems restated (the untyped's capability holds index 0; nothing carved remains below its index), and the deleted code removed.  Exerciser: `untyped-reset` reads 0 at first call and steady state |

### Part 12 in steps (each compiles; proofs land with or before the code they cover)

The TCB holds its slots in fixed-size fields (`spaceCells`, two cells; `spaceLinks`, their link words, the same layout as `CNode.cells` and its links).  Slot readers and writers dispatch on the object kind, the `.cnode` arm being today's function, so every CNode theorem is reused.  This adds no store lookup on the context switch or the IPC-buffer fill.  A companion CNode per TCB was rejected: it needs a second object per retype and a second erase, it adds a lookup to every root read, and seL4's TCB slots are inside the TCB.

1. **12.1 Roots are slot reads.**  `TCB.cspaceRoot` / `vspaceRoot` become definitions reading cells 0 and 1, with a setter `TCB.withSpaceCaps` and its simp lemmas; boot and `objectOfKernelType .tcb` fill the cells.  Behaviour is unchanged.
2. **12.2 Object-slot dispatch.**  The slot-link readers and writers, `linksOnlyWrite`, `objectsAgreeOffDerivationLinks`, `cdtCompleteness`, `cspaceLookupSound`, `replyCapPointsToValidReply` and `capabilityBadgesWellFormed` read slots through the dispatch; the information-flow projection of a TCB hides its link words; the runtime slot checks cover TCB slots.  No TCB slot is in the tree yet.
3. **12.3 Delete, revoke and finality reach TCB slots** (`cspaceDeleteSlotCore`, the finalising delete, `revokeFirstChildLoop`, `cnodeSlotsUnreferenced`, `objectNamesListed`'s TCB arm), with the delete and revoke preservation restated.
4. **12.4 Teardown.**  A thread's cleanup splices its two slots out (`detachTcbSlots`), as a CNode's cleanup splices its slots.
5. **12.5 The copying set-space, proven.**  As seL4: the old slot content is deleted, then the copy is inserted with the edge from its source slot; the capability, link and information-flow bundles are proven.
6. **12.6 Live.**  The set-space resolver returns the source slots and the dispatcher runs 12.5; the old `setThreadSpace` is deleted.

