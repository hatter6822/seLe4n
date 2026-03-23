/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Machine
import SeLe4n.Kernel.RobinHood

namespace SeLe4n.Model


/-- Stable service identity metadata for graph-level orchestration. -/
structure ServiceIdentity where
  sid : ServiceId
  backingObject : SeLe4n.ObjId
  owner : SeLe4n.ObjId
  deriving Repr, DecidableEq

/-- Declared service dependencies and isolation edges.

WS-Q1-E1: `status` field removed — runtime lifecycle state is no longer tracked
in the service graph. The capability-indexed service registry
(`SystemState.serviceRegistry`) replaces lifecycle-focused orchestration. -/
structure ServiceGraphEntry where
  identity : ServiceIdentity
  dependencies : List ServiceId
  isolatedFrom : List ServiceId
  deriving Repr, DecidableEq

inductive AccessRight where
  | read
  | write
  | grant
  | grantReply
  | retype        -- WS-H15c/A-42: lifecycle retype operations
  deriving Repr, DecidableEq

namespace AccessRight

/-- WS-F5/D2a: Ordinal encoding for bitmask representation. Each right maps to
    a unique bit position. -/
@[inline] def toBit : AccessRight → Nat
  | .read       => 0
  | .write      => 1
  | .grant      => 2
  | .grantReply => 3
  | .retype     => 4

/-- WS-F5/D2a: All access rights in canonical order (bit 0..4). -/
def all : List AccessRight := [.read, .write, .grant, .grantReply, .retype]

end AccessRight

/-- WS-F5/D2a: Order-independent access right set using bitmask representation.

Matches seL4's rights representation as a word-sized bitmask. Each of the 5
access rights maps to a unique bit position (0..4). Membership is a single
bit test; subset is bitwise AND comparison. Two sets with the same rights in
any order are structurally equal. -/
structure AccessRightSet where
  bits : Nat
deriving DecidableEq, Repr, Inhabited

namespace AccessRightSet

/-- S1-G: Maximum valid bitmask value — 5 access rights use bits 0..4,
    so valid values are in `[0, 2^5)`. -/
private def maxBits : Nat := 2 ^ 5

/-- S1-G: Well-formedness predicate — a rights set is valid when its bitmask
    fits in the 5-bit rights space (bits 0..4). Values ≥ 32 have spurious
    upper bits that do not correspond to any access right. -/
@[inline] def valid (s : AccessRightSet) : Prop := s.bits < maxBits

instance (s : AccessRightSet) : Decidable s.valid :=
  inferInstanceAs (Decidable (s.bits < maxBits))

/-- S1-G: Construct a rights set from a raw `Nat`, masking to the valid 5-bit
    range. This is the safe constructor — it guarantees `valid` by construction. -/
@[inline] def ofNat (n : Nat) : AccessRightSet := ⟨n % maxBits⟩

/-- S1-G: `ofNat` always produces a valid rights set. -/
theorem ofNat_valid (n : Nat) : (ofNat n).valid := by
  simp [ofNat, valid, maxBits]
  exact Nat.mod_lt n (by decide)

/-- S1-G: `ofNat` is idempotent on valid inputs. -/
theorem ofNat_idempotent (s : AccessRightSet) (h : s.valid) :
    ofNat s.bits = s := by
  simp [ofNat, maxBits, valid] at *
  exact congrArg AccessRightSet.mk (Nat.mod_eq_of_lt h)

/-- The empty rights set (no permissions). -/
@[inline] def empty : AccessRightSet := ⟨0⟩

/-- Construct a rights set from a single right. -/
@[inline] def singleton (r : AccessRight) : AccessRightSet := ⟨1 <<< r.toBit⟩

/-- WS-F5/D2a: Construct a rights set from a list of rights. Order-independent:
    `ofList [.read, .write] = ofList [.write, .read]`. -/
@[inline] def ofList (rs : List AccessRight) : AccessRightSet :=
  ⟨rs.foldl (fun acc r => acc ||| (1 <<< r.toBit)) 0⟩

/-- WS-F5/D2a: Membership test — O(1) bit check. -/
@[inline] def mem (s : AccessRightSet) (r : AccessRight) : Bool :=
  (s.bits >>> r.toBit) &&& 1 != 0

instance : Membership AccessRight AccessRightSet where
  mem s r := AccessRightSet.mem s r = true

instance (r : AccessRight) (s : AccessRightSet) : Decidable (r ∈ s) :=
  inferInstanceAs (Decidable (AccessRightSet.mem s r = true))

/-- WS-F5/D2a: Subset test — O(1) bitwise check. `a ⊆ b` iff every bit in `a`
    is also set in `b`. -/
@[inline] def subset (a b : AccessRightSet) : Bool :=
  a.bits &&& b.bits == a.bits

/-- WS-F5/D2a: Union of two rights sets (bitwise OR). -/
@[inline] def union (a b : AccessRightSet) : AccessRightSet := ⟨a.bits ||| b.bits⟩

/-- WS-F5/D2a: Intersection of two rights sets (bitwise AND). -/
@[inline] def inter (a b : AccessRightSet) : AccessRightSet := ⟨a.bits &&& b.bits⟩

/-- WS-F5/D2a: Convert rights set to a list (canonical order). -/
def toList (s : AccessRightSet) : List AccessRight :=
  AccessRight.all.filter s.mem

instance : ToString AccessRightSet where
  toString s := toString (s.toList.map reprStr)

/-- WS-F5/D2a: `ofList` is order-independent — permutations produce equal sets. -/
theorem ofList_comm (a b : AccessRight) (rest : List AccessRight) :
    ofList (a :: b :: rest) = ofList (b :: a :: rest) := by
  simp [ofList, List.foldl]
  congr 1
  exact Nat.or_comm (1 <<< a.toBit) (1 <<< b.toBit)

/-- T2-A (H-1): Helper — each `AccessRight.toBit` yields a value < 5, so
    `1 <<< r.toBit < maxBits` (i.e., < 32). -/
private theorem singleton_lt_maxBits (r : AccessRight) : 1 <<< r.toBit < maxBits := by
  cases r <;> simp [AccessRight.toBit, maxBits] <;> decide

/-- T2-A (H-1): Helper — bitwise OR of two values below `2^n` stays
    below `2^n`. This holds because OR cannot set bits that neither
    operand has, and both operands fit in n bits. -/
private theorem or_lt_two_pow (a b : Nat) (n : Nat) (ha : a < 2^n) (hb : b < 2^n) :
    a ||| b < 2^n :=
  Nat.or_lt_two_pow ha hb

private theorem or_lt_maxBits (a b : Nat) (ha : a < maxBits) (hb : b < maxBits) :
    a ||| b < maxBits :=
  or_lt_two_pow a b 5 ha hb

/-- T2-A (H-1): The fold body preserves `< maxBits` — accumulating one more
    singleton via OR stays within the 5-bit range. -/
private theorem foldl_or_lt_maxBits (rs : List AccessRight) (init : Nat)
    (hInit : init < maxBits) :
    rs.foldl (fun acc r => acc ||| (1 <<< r.toBit)) init < maxBits := by
  induction rs generalizing init with
  | nil => exact hInit
  | cons r rest ih =>
    simp only [List.foldl_cons]
    exact ih _ (or_lt_maxBits init (1 <<< r.toBit) hInit (singleton_lt_maxBits r))

/-- T2-A (H-1): `ofList` always produces a valid rights set.

    **Proof sketch**: `ofList` folds `(fun acc r => acc ||| (1 <<< r.toBit))`
    starting from 0. Each `1 <<< r.toBit` is < 32 (since `toBit` ∈ {0..4}),
    and bitwise OR of values < 32 stays < 32. Therefore the result fits in
    the 5-bit rights space, satisfying `valid` (`.bits < 2^5`).

    This closes finding H-1: `AccessRightSet.ofList` now has a machine-checked
    `valid` postcondition. -/
theorem ofList_valid (rs : List AccessRight) : (ofList rs).valid := by
  simp [ofList, valid]
  exact foldl_or_lt_maxBits rs 0 (by unfold maxBits; omega)

end AccessRightSet

/-- The addressable target of a capability in the abstract object universe.

WS-E4/M-12: Added `replyCap` variant for one-shot reply capabilities that
reference a specific sender's TCB, enabling bidirectional IPC. -/
inductive CapTarget where
  | object (id : SeLe4n.ObjId)
  | cnodeSlot (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot)
  | replyCap (senderTcb : SeLe4n.ThreadId)
  deriving Repr, DecidableEq

/-- WS-F5/D2b: Capability with order-independent rights set.
    `rights` is an `AccessRightSet` (bitmask), replacing the prior `List AccessRight`. -/
structure Capability where
  target : CapTarget
  rights : AccessRightSet
  badge : Option SeLe4n.Badge := none
  deriving Repr, DecidableEq

namespace Capability

/-- WS-F5/D2b: Check if a capability has a specific right. O(1) bit test. -/
def hasRight (cap : Capability) (right : AccessRight) : Bool :=
  cap.rights.mem right

end Capability

/-- WS-H12d/A-09: Maximum number of message registers per IPC message.
Matches seL4's `seL4_MsgMaxLength` (120 words). -/
def maxMessageRegisters : Nat := 120

/-- WS-H12d/A-09: Maximum number of extra capabilities per IPC message.
Matches seL4's `seL4_MsgMaxExtraCaps` (3 extra caps). -/
def maxExtraCaps : Nat := 3

/-- WS-E4/M-02: Structured IPC message payload for endpoint transfers.

Models seL4 message registers plus optional capability transfer and sender badge.
WS-H12d/A-09: Registers and caps are bounded `Array` types matching seL4's
`seL4_MsgMaxLength` (120) and `seL4_MsgMaxExtraCaps` (3). Bounds are enforced
at IPC send boundaries. -/
structure IpcMessage where
  /-- S4-D: Changed from `Array Nat` to `Array RegValue` for type consistency
      with the machine register model. All register values in IPC messages
      are now typed, matching the `RegValue` wrapper used throughout the
      register decode and context-switch infrastructure. -/
  registers : Array SeLe4n.RegValue
  caps : Array Capability := #[]
  badge : Option SeLe4n.Badge := none
  deriving Repr, DecidableEq

namespace IpcMessage

def empty : IpcMessage := { registers := (#[] : Array SeLe4n.RegValue), caps := #[], badge := none }

/-- WS-H12d/A-09: Predicate asserting that a message's payload respects
seL4 message-register and extra-capability bounds. -/
def bounded (msg : IpcMessage) : Prop :=
  msg.registers.size ≤ maxMessageRegisters ∧
  msg.caps.size ≤ maxExtraCaps

/-- WS-H12d/A-09: Decidable bounds check for runtime enforcement at IPC
send boundaries. Returns `true` iff the message satisfies payload bounds. -/
def checkBounds (msg : IpcMessage) : Bool :=
  msg.registers.size ≤ maxMessageRegisters &&
  msg.caps.size ≤ maxExtraCaps

theorem empty_bounded : IpcMessage.empty.bounded := by
  unfold bounded empty maxMessageRegisters maxExtraCaps
  simp [Array.size]

theorem checkBounds_iff_bounded (msg : IpcMessage) :
    msg.checkBounds = true ↔ msg.bounded := by
  unfold checkBounds bounded maxMessageRegisters maxExtraCaps
  simp [Bool.and_eq_true]

end IpcMessage

/-- M-D01: Result of attempting to unwrap a single transferred capability
into the receiver's CSpace during IPC rendezvous.

seL4 semantics: each extra cap in the message is independently unwrapped.
Failures on one cap do not abort the transfer of subsequent caps. -/
inductive CapTransferResult where
  /-- Successfully installed in the receiver's CSpace at the given CNode and slot. -/
  | installed (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot)
  /-- No empty slot available in the receiver's CNode (receiver CSpace full). -/
  | noSlot
  /-- The endpoint capability lacks the Grant right — transfer silently skipped. -/
  | grantDenied
  deriving Repr, DecidableEq

/-- M-D01: Aggregated results of unwrapping all extra capabilities in an
IPC message. One entry per cap in the original `msg.caps` array. -/
structure CapTransferSummary where
  results : Array CapTransferResult := #[]
  deriving Repr, DecidableEq

/-- Per-thread IPC scheduler-visible status.

WS-E3/H-09: Endpoint-local blocking states for deterministic handshake.
WS-E4/M-12: Added `blockedOnReply` for bidirectional IPC (sender waiting for reply).
WS-H1/C-01: Added `blockedOnCall` — a Call sender blocked on the send queue carries
  this state (distinct from `blockedOnSend`) so that upon dequeue the sender
  transitions to `blockedOnReply`, not `.ready`.
WS-H1/M-02: `blockedOnReply` now carries an optional `replyTarget` recording which
  server thread is authorized to reply, preventing confused-deputy attacks. -/
inductive ThreadIpcState where
  | ready
  | blockedOnSend (endpoint : SeLe4n.ObjId)
  | blockedOnReceive (endpoint : SeLe4n.ObjId)
  | blockedOnNotification (notification : SeLe4n.ObjId)
  | blockedOnReply (endpoint : SeLe4n.ObjId) (replyTarget : Option SeLe4n.ThreadId := none)
  | blockedOnCall (endpoint : SeLe4n.ObjId)
  deriving Repr, DecidableEq

/-- Thread Control Block.

M-03/WS-E6: `deadline` field for EDF tie-breaking. Default 0 = no deadline.
M-04/WS-E6: `timeSlice` field for preemption. Default 5 ticks per quantum. -/
inductive QueuePPrev where
  | endpointHead
  | tcbNext (tid : SeLe4n.ThreadId)
  deriving Repr, DecidableEq

structure TCB where
  tid : SeLe4n.ThreadId
  priority : SeLe4n.Priority
  domain : SeLe4n.DomainId
  cspaceRoot : SeLe4n.ObjId
  vspaceRoot : SeLe4n.ObjId
  ipcBuffer : SeLe4n.VAddr
  ipcState : ThreadIpcState := .ready
  /-- M-04/WS-E6: Remaining time-slice ticks before preemption. Reset to
      `defaultTimeSlice` on expiry. Default value matches seL4's
      CONFIG_TIMER_TICK_MS-based quantum. -/
  timeSlice : Nat := 5
  /-- M-03/WS-E6: Scheduling deadline for EDF tie-breaking within same
      priority level. 0 = no deadline (lowest urgency). Lower nonzero
      values are more urgent. -/
  deadline : SeLe4n.Deadline := ⟨0⟩
  /-- WS-E4/M-01 intrusive queue linkage for endpoint dual queues.
      `none`/`none` means detached from intrusive endpoint wait queues. -/
  queuePrev : Option SeLe4n.ThreadId := none
  /-- WS-E8: pointer-to-previous-link metadata.
      `endpointHead` means this node is currently referenced by queue head;
      `tcbNext prevTid` means it is referenced by `prevTid.queueNext`.
      Cleared when detached from intrusive endpoint wait queues. -/
  queuePPrev : Option QueuePPrev := none
  queueNext : Option SeLe4n.ThreadId := none
  /-- WS-F1: Pending IPC message for transfer during endpoint rendezvous.
      Stored in the sender's TCB while blocked; transferred to the receiver
      on handshake/dequeue. `none` = no pending message. -/
  pendingMessage : Option IpcMessage := none
  /-- WS-H12c/H-03: Per-TCB register save area. The scheduler saves the
      outgoing thread's machine registers here on dispatch and restores
      the incoming thread's context from here. Zero-initialized by default.
      See `contextMatchesCurrent` in `Scheduler/Invariant.lean`. -/
  registerContext : SeLe4n.RegisterFile := default
  /-- R7-D/L-06: Capability pointer to the fault handler endpoint.
      In seL4, when a thread faults (e.g., VM fault, cap fault), the kernel
      sends a fault IPC message to the endpoint identified by this capability.
      `none` = no fault handler configured (faults are silently dropped). -/
  faultHandler : Option SeLe4n.CPtr := none
  /-- R7-D/L-06: Object ID of the bound notification object.
      In seL4, a thread may bind one notification object. Signals on the bound
      notification can wake the thread when it is waiting on an endpoint.
      `none` = no bound notification. -/
  boundNotification : Option SeLe4n.ObjId := none
  deriving Repr

/-- WS-H12c: Manual `BEq` for `TCB`. `DecidableEq` cannot be derived because
`RegisterFile` contains a function field (`gpr : Nat → Nat`). Field-wise
comparison uses the `BEq RegisterFile` instance from `Machine.lean`. -/
instance : BEq TCB where
  beq a b :=
    a.tid == b.tid && a.priority == b.priority && a.domain == b.domain &&
    a.cspaceRoot == b.cspaceRoot && a.vspaceRoot == b.vspaceRoot &&
    a.ipcBuffer == b.ipcBuffer && a.ipcState == b.ipcState &&
    a.timeSlice == b.timeSlice && a.deadline == b.deadline &&
    a.queuePrev == b.queuePrev && a.queuePPrev == b.queuePPrev &&
    a.queueNext == b.queueNext && a.pendingMessage == b.pendingMessage &&
    a.registerContext == b.registerContext &&
    a.faultHandler == b.faultHandler && a.boundNotification == b.boundNotification

/-- Intrusive FIFO queue metadata for endpoint wait queues.

Queue membership links are stored in the waiting TCBs (`queuePrev`/`queueNext`).
The endpoint stores only queue boundaries. -/
structure IntrusiveQueue where
  head : Option SeLe4n.ThreadId := none
  tail : Option SeLe4n.ThreadId := none
  deriving Repr, DecidableEq

/-- Endpoint object model.

WS-H12a: Endpoint structure uses only intrusive dual-queue fields.
Legacy WS-E3 fields (`state`, `queue`, `waitingReceiver`) and the
`EndpointState` type have been removed — all IPC operations use the O(1)
dual-queue path (`endpointSendDual`/`endpointReceiveDual`). -/
structure Endpoint where
  sendQ : IntrusiveQueue := {}
  receiveQ : IntrusiveQueue := {}
  deriving Repr, DecidableEq

inductive NotificationState where
  | idle
  | waiting
  | active
  deriving Repr, DecidableEq

/-- Minimal notification object model for WS-B6.

`active` stores a single pending badge, while `waiting` tracks blocked receivers.

**S4-G: `waitingThreads` representation evaluation.** An intrusive queue
(matching the endpoint dual-queue design) was evaluated and not implemented:

1. **Low cardinality.** Unlike endpoint send/receive queues which can grow to
   hundreds of threads in server workloads, notification waiting lists are
   typically short (1-3 threads). The seL4 spec notes that most notifications
   are 1:1 or 1:N with small N.

2. **No ordering requirement.** `notificationSignal` wakes the head waiter
   (`List.head?`), but seL4 does not guarantee FIFO ordering for notification
   waiters. Any waiter may be woken, so the prepend-based O(1) enqueue in
   `notificationWait` is semantically correct.

3. **O(n) cost is acceptable.** The only O(n) operation is
   `List.filter` in `removeFromAllNotificationWaitLists` (lifecycle cleanup),
   which iterates over all notifications' waiting lists during TCB deletion.
   With the expected bound of ≤8 waiters per notification (typical RPi5 core
   count), this is effectively O(1).

4. **Migration cost.** Intrusive queues require adding `notifQueuePrev`/
   `notifQueueNext` fields to TCB (6 new fields including PPrev metadata),
   duplicating the endpoint queue infrastructure for minimal benefit.

The `List` representation is retained. If future profiling reveals notification
queue pressure, migration to intrusive queues remains straightforward. -/
structure Notification where
  state : NotificationState
  waitingThreads : List SeLe4n.ThreadId
  pendingBadge : Option SeLe4n.Badge := none
  deriving Repr, DecidableEq

/-- WS-H13/H-01: Depth-aware CNode with compressed-path guard.

`depth` = maximum remaining CSpace depth in bits from this node to any leaf.
Each resolution step consumes `guardWidth + radixWidth` bits.
A large `guardWidth` compresses an unbranched path prefix into a single
guard comparison, avoiding chains of intermediate CNodes (Patricia-trie
optimisation matching seL4's real CSpace implementation).

`slots` is backed by `RHTable Slot Capability` — a formally verified Robin Hood
hash table providing O(1) amortized lookup, insert, and delete with machine-checked
proofs (WS-N). Key uniqueness is enforced by the `noDupKeys` invariant. -/
structure CNode where
  depth      : Nat          -- maximum remaining depth in bits from this node to any leaf
  guardWidth : Nat          -- width of guard field in bits
  guardValue : Nat          -- expected guard value to match
  radixWidth : Nat          -- width of slot index in bits (2^radixWidth slots)
  slots      : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.Slot Capability
  deriving Repr

/-- Maximum CSpace address width (matching ARM64 word size). -/
def maxCSpaceDepth : Nat := 64

/-- WS-F2: Child allocation record within an untyped memory region.
Each child records the object identity, its byte offset within the parent
untyped region, and its allocation size. -/
structure UntypedChild where
  objId : SeLe4n.ObjId
  offset : Nat
  size : Nat
  deriving Repr, DecidableEq

/-- WS-F2: Untyped memory object — the foundational seL4 memory safety mechanism.

Models a contiguous region of physical memory `[regionBase, regionBase + regionSize)`
from which typed kernel objects are carved via `retypeFromUntyped`. The `watermark`
tracks the next free byte offset within the region (monotonically increasing).

seL4 reference: `Untyped_D` in the abstract spec — tracks device/non-device flag,
region bounds, and a free-area pointer. Our model uses an explicit child list for
non-overlap proofs rather than relying on CSpace derivation tree ancestry. -/
structure UntypedObject where
  /-- Base physical address of the untyped region. -/
  regionBase : SeLe4n.PAddr
  /-- Total size of the region in bytes. -/
  regionSize : Nat
  /-- Next free byte offset within the region. Monotonically increasing.
      Invariant: `watermark ≤ regionSize`. -/
  watermark : Nat := 0
  /-- List of typed objects carved from this region. Each child records
      its ObjId, offset within the region, and size. -/
  children : List UntypedChild := []
  /-- Whether this untyped covers device memory (MMIO). Device untypeds
      cannot back TCBs, CNodes, or other kernel objects. -/
  isDevice : Bool := false
  deriving Repr, DecidableEq

namespace UntypedObject

/-- Remaining free space in the untyped region. -/
def freeSpace (ut : UntypedObject) : Nat :=
  ut.regionSize - ut.watermark

/-- Check whether an allocation of `size` bytes fits within the remaining region. -/
def canAllocate (ut : UntypedObject) (size : Nat) : Bool :=
  size > 0 && ut.watermark + size ≤ ut.regionSize

/-- Allocate `size` bytes from the region, returning the updated untyped and
    the byte offset of the new allocation.

    S4-H: New children are prepended to the `children` list, creating
    reverse-chronological order (most recent allocation first). Proofs that
    traverse children must account for this ordering — in particular,
    `List.mem` witnesses are preserved across allocations since prepending
    does not remove existing elements. -/
def allocate (ut : UntypedObject) (childId : SeLe4n.ObjId) (size : Nat) :
    Option (UntypedObject × Nat) :=
  if ut.canAllocate size then
    let offset := ut.watermark
    some ({ ut with
      watermark := ut.watermark + size
      children := { objId := childId, offset := offset, size := size } :: ut.children
    }, offset)
  else
    none

/-- Reset the untyped to its initial state (revoke all children). -/
def reset (ut : UntypedObject) : UntypedObject :=
  { ut with watermark := 0, children := [] }

/-- Watermark is within region bounds. -/
def watermarkValid (ut : UntypedObject) : Prop :=
  ut.watermark ≤ ut.regionSize

/-- All children fit within the watermark (and thus within the region). -/
def childrenWithinWatermark (ut : UntypedObject) : Prop :=
  ∀ c ∈ ut.children, c.offset + c.size ≤ ut.watermark

/-- No two children overlap in the allocated region. -/
def childrenNonOverlap (ut : UntypedObject) : Prop :=
  ∀ c₁ c₂, c₁ ∈ ut.children → c₂ ∈ ut.children →
    c₁ ≠ c₂ → c₁.offset + c₁.size ≤ c₂.offset ∨ c₂.offset + c₂.size ≤ c₁.offset

/-- Children have distinct object identities. -/
def childrenUniqueIds (ut : UntypedObject) : Prop :=
  ∀ c₁ c₂, c₁ ∈ ut.children → c₂ ∈ ut.children →
    c₁.objId = c₂.objId → c₁ = c₂

/-- Combined well-formedness predicate for the untyped object. -/
def wellFormed (ut : UntypedObject) : Prop :=
  ut.watermarkValid ∧ ut.childrenWithinWatermark ∧
  ut.childrenNonOverlap ∧ ut.childrenUniqueIds

theorem empty_watermarkValid (base : SeLe4n.PAddr) (size : Nat) :
    (UntypedObject.mk base size 0 [] false).watermarkValid := by
  simp [watermarkValid]

theorem empty_childrenWithinWatermark (base : SeLe4n.PAddr) (size : Nat) :
    (UntypedObject.mk base size 0 [] false).childrenWithinWatermark := by
  intro c hMem
  simp at hMem

theorem empty_childrenNonOverlap (base : SeLe4n.PAddr) (size : Nat) :
    (UntypedObject.mk base size 0 [] false).childrenNonOverlap := by
  intro c₁ c₂ hMem₁
  simp at hMem₁

theorem empty_childrenUniqueIds (base : SeLe4n.PAddr) (size : Nat) :
    (UntypedObject.mk base size 0 [] false).childrenUniqueIds := by
  intro c₁ c₂ hMem₁
  simp at hMem₁

theorem empty_wellFormed (base : SeLe4n.PAddr) (size : Nat) :
    (UntypedObject.mk base size 0 [] false).wellFormed :=
  ⟨empty_watermarkValid base size, empty_childrenWithinWatermark base size,
   empty_childrenNonOverlap base size, empty_childrenUniqueIds base size⟩

/-- `canAllocate` being true implies the allocation fits within region bounds. -/
theorem canAllocate_implies_fits (ut : UntypedObject) (size : Nat)
    (hCan : ut.canAllocate size = true) :
    ut.watermark + size ≤ ut.regionSize := by
  simp [canAllocate] at hCan
  exact hCan.2

/-- Decomposition lemma: a successful `allocate` produces a specific updated state. -/
theorem allocate_some_iff (ut : UntypedObject) (childId : SeLe4n.ObjId) (size : Nat)
    (result : UntypedObject × Nat) :
    ut.allocate childId size = some result ↔
      ut.canAllocate size = true ∧
      result = ({ ut with
        watermark := ut.watermark + size
        children := { objId := childId, offset := ut.watermark, size := size } :: ut.children
      }, ut.watermark) := by
  constructor
  · intro h
    unfold allocate at h
    by_cases hCan : ut.canAllocate size
    · simp [hCan] at h; exact ⟨hCan, h.symm⟩
    · simp [hCan] at h
  · intro ⟨hCan, hEq⟩
    unfold allocate
    simp [hCan, hEq]

/-- After a successful `allocate`, the watermark advances by exactly `size`. -/
theorem allocate_watermark_advance (ut ut' : UntypedObject) (childId : SeLe4n.ObjId)
    (size offset : Nat) (hAlloc : ut.allocate childId size = some (ut', offset)) :
    ut'.watermark = ut.watermark + size := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_, hEq⟩
  have hU := (Prod.mk.inj hEq).1
  subst hU; rfl

/-- After a successful `allocate`, the returned offset equals the pre-allocation watermark. -/
theorem allocate_offset_eq_watermark (ut ut' : UntypedObject) (childId : SeLe4n.ObjId)
    (size offset : Nat) (hAlloc : ut.allocate childId size = some (ut', offset)) :
    offset = ut.watermark := by
  rw [allocate_some_iff] at hAlloc
  exact (Prod.mk.inj hAlloc.2).2

/-- Watermark monotonicity: a successful allocation never decreases the watermark. -/
theorem allocate_watermark_monotone (ut ut' : UntypedObject) (childId : SeLe4n.ObjId)
    (size offset : Nat) (hAlloc : ut.allocate childId size = some (ut', offset)) :
    ut.watermark ≤ ut'.watermark := by
  have hAdv := allocate_watermark_advance ut ut' childId size offset hAlloc
  omega

/-- A successful allocation preserves watermark validity when the pre-state is valid. -/
theorem allocate_preserves_watermarkValid (ut ut' : UntypedObject) (childId : SeLe4n.ObjId)
    (size offset : Nat) (_hWF : ut.watermarkValid)
    (hAlloc : ut.allocate childId size = some (ut', offset)) :
    ut'.watermarkValid := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨hCan, hEq⟩
  have hFits := canAllocate_implies_fits ut size hCan
  have hU := (Prod.mk.inj hEq).1
  subst hU; simp [watermarkValid]; omega

/-- `allocate` does not change the region base or size. -/
theorem allocate_preserves_region (ut ut' : UntypedObject) (childId : SeLe4n.ObjId)
    (size offset : Nat) (hAlloc : ut.allocate childId size = some (ut', offset)) :
    ut'.regionBase = ut.regionBase ∧ ut'.regionSize = ut.regionSize := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_, hEq⟩
  have hU := (Prod.mk.inj hEq).1
  subst hU; exact ⟨rfl, rfl⟩

/-- WS-F2: A successful allocation preserves childrenWithinWatermark.
Existing children are within the old watermark (≤ new watermark), and the new
child occupies [old_watermark, old_watermark + size] = [old_watermark, new_watermark]. -/
theorem allocate_preserves_childrenWithinWatermark (ut ut' : UntypedObject)
    (childId : SeLe4n.ObjId) (size offset : Nat)
    (hBounds : ut.childrenWithinWatermark)
    (hAlloc : ut.allocate childId size = some (ut', offset)) :
    ut'.childrenWithinWatermark := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_hCan, hEq⟩
  have hU := (Prod.mk.inj hEq).1; subst hU
  intro c hMem
  simp at hMem ⊢
  rcases hMem with rfl | hOld
  · dsimp; omega
  · have := hBounds c hOld; omega

/-- WS-F2: A successful allocation preserves childrenNonOverlap, given that
existing children are within the watermark. Since the new child starts at the
old watermark and all existing children end at or before the old watermark,
no overlap is possible. -/
theorem allocate_preserves_childrenNonOverlap (ut ut' : UntypedObject)
    (childId : SeLe4n.ObjId) (size offset : Nat)
    (hNonOverlap : ut.childrenNonOverlap)
    (hBounds : ut.childrenWithinWatermark)
    (hAlloc : ut.allocate childId size = some (ut', offset)) :
    ut'.childrenNonOverlap := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_hCan, hEq⟩
  have hU := (Prod.mk.inj hEq).1; subst hU
  intro c₁ c₂ hMem₁ hMem₂ hNe
  simp at hMem₁ hMem₂
  rcases hMem₁ with rfl | hOld₁ <;> rcases hMem₂ with rfl | hOld₂
  · exact absurd rfl hNe
  · -- new child vs old child: old child ends ≤ watermark = new child offset
    right; have := hBounds c₂ hOld₂; dsimp; omega
  · -- old child vs new child: old child ends ≤ watermark = new child offset
    left; have := hBounds c₁ hOld₁; dsimp; omega
  · -- two old children: by pre-condition
    exact hNonOverlap c₁ c₂ hOld₁ hOld₂ hNe

/-- WS-F2: A successful allocation preserves childrenUniqueIds, given that
the new child's ID does not collide with any existing child. -/
theorem allocate_preserves_childrenUniqueIds (ut ut' : UntypedObject)
    (childId : SeLe4n.ObjId) (size offset : Nat)
    (hUnique : ut.childrenUniqueIds)
    (hFresh : ∀ c ∈ ut.children, c.objId ≠ childId)
    (hAlloc : ut.allocate childId size = some (ut', offset)) :
    ut'.childrenUniqueIds := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_hCan, hEq⟩
  have hU := (Prod.mk.inj hEq).1; subst hU
  intro c₁ c₂ hMem₁ hMem₂ hIdEq
  simp at hMem₁ hMem₂
  rcases hMem₁ with rfl | hOld₁ <;> rcases hMem₂ with rfl | hOld₂
  · rfl
  · -- new child has objId = childId, old child has objId ≠ childId
    dsimp at hIdEq; exact absurd hIdEq.symm (hFresh c₂ hOld₂)
  · dsimp at hIdEq; exact absurd hIdEq (hFresh c₁ hOld₁)
  · exact hUnique c₁ c₂ hOld₁ hOld₂ hIdEq

/-- `reset` restores watermark validity. -/
theorem reset_watermarkValid (ut : UntypedObject) : ut.reset.watermarkValid := by
  simp [reset, watermarkValid]

/-- `reset` restores full well-formedness. -/
theorem reset_wellFormed (ut : UntypedObject) : ut.reset.wellFormed := by
  refine ⟨reset_watermarkValid ut, ?_, ?_, ?_⟩
  · intro c hMem; simp [reset] at hMem
  · intro c₁ c₂ hMem₁; simp [reset] at hMem₁
  · intro c₁ c₂ hMem₁; simp [reset] at hMem₁

end UntypedObject

-- ============================================================================
-- Syscall decode types — register-sourced syscall argument decoding
-- ============================================================================

/-- Typed syscall identifier covering the modeled syscall set.
    Maps to the syscall number register value (x7 on ARM64).
    Each variant corresponds to exactly one kernel API entry point. -/
inductive SyscallId where
  | send
  | receive
  | call
  | reply
  | cspaceMint
  | cspaceCopy
  | cspaceMove
  | cspaceDelete
  | lifecycleRetype
  | vspaceMap
  | vspaceUnmap
  | serviceRegister   -- WS-Q1-D: capability-mediated service registration
  | serviceRevoke     -- WS-Q1-D: service revocation
  | serviceQuery      -- WS-Q1-D: service lookup by capability
  deriving Repr, DecidableEq, Inhabited

namespace SyscallId

/-- Encode a syscall identifier to its numeric value for the syscall number
    register. The encoding matches the canonical ordering and is injective. -/
@[inline] def toNat : SyscallId → Nat
  | .send            => 0
  | .receive         => 1
  | .call            => 2
  | .reply           => 3
  | .cspaceMint      => 4
  | .cspaceCopy      => 5
  | .cspaceMove      => 6
  | .cspaceDelete    => 7
  | .lifecycleRetype => 8
  | .vspaceMap       => 9
  | .vspaceUnmap     => 10
  | .serviceRegister => 11
  | .serviceRevoke   => 12
  | .serviceQuery    => 13

/-- Total number of modeled syscalls. -/
def count : Nat := 14

/-- Decode a natural number to a syscall identifier.
    Returns `none` for values outside the modeled set. -/
@[inline] def ofNat? : Nat → Option SyscallId
  | 0  => some .send
  | 1  => some .receive
  | 2  => some .call
  | 3  => some .reply
  | 4  => some .cspaceMint
  | 5  => some .cspaceCopy
  | 6  => some .cspaceMove
  | 7  => some .cspaceDelete
  | 8  => some .lifecycleRetype
  | 9  => some .vspaceMap
  | 10 => some .vspaceUnmap
  | 11 => some .serviceRegister
  | 12 => some .serviceRevoke
  | 13 => some .serviceQuery
  | _  => none

instance : ToString SyscallId where
  toString
    | .send            => "send"
    | .receive         => "receive"
    | .call            => "call"
    | .reply           => "reply"
    | .cspaceMint      => "cspaceMint"
    | .cspaceCopy      => "cspaceCopy"
    | .cspaceMove      => "cspaceMove"
    | .cspaceDelete    => "cspaceDelete"
    | .lifecycleRetype => "lifecycleRetype"
    | .vspaceMap       => "vspaceMap"
    | .vspaceUnmap     => "vspaceUnmap"
    | .serviceRegister => "serviceRegister"
    | .serviceRevoke   => "serviceRevoke"
    | .serviceQuery    => "serviceQuery"

/-- Round-trip: encoding then decoding a SyscallId recovers the original. -/
theorem ofNat_toNat (s : SyscallId) : SyscallId.ofNat? s.toNat = some s := by
  cases s <;> rfl

/-- Round-trip: decoding then encoding preserves the numeric value.

S4-I: This proof uses a uniform `match`/`simp`/`subst` pattern for each of
the 14 syscall variants plus a wildcard case. The `cases s <;> rfl` approach
used for `ofNat_toNat` is not applicable here because the hypothesis is on `n`
(a `Nat`) rather than on a finite inductive type. A `decide`-based approach
would require `BEq`/`DecidableEq` on the `Option SyscallId × Nat` pair and
scales poorly for larger enums. The current explicit case enumeration is the
most robust approach for Lean 4's pattern matching. -/
theorem toNat_ofNat {n : Nat} {s : SyscallId} (h : SyscallId.ofNat? n = some s) :
    s.toNat = n := by
  revert s
  match n with
  | 0  | 1  | 2  | 3  | 4  | 5  | 6
  | 7  | 8  | 9  | 10 | 11 | 12 | 13 =>
    intro s h; simp [ofNat?] at h; subst h; rfl
  | n + 14 => intro s h; simp [ofNat?] at h

/-- Injectivity: the toNat encoding is injective. -/
theorem toNat_injective {a b : SyscallId} (h : a.toNat = b.toNat) : a = b := by
  have ha := ofNat_toNat a
  have hb := ofNat_toNat b
  rw [h] at ha
  rw [ha] at hb
  exact Option.some.inj hb

end SyscallId

/-- Decoded message-info word layout, matching seL4's `seL4_MessageInfo_t`.
    Encodes the metadata carried in the message-info register (x1 on ARM64):
    - `length`: number of message registers used (0..120)
    - `extraCaps`: number of extra capabilities transferred (0..3)
    - `label`: user-specified label/tag for message discrimination -/
structure MessageInfo where
  length    : Nat
  extraCaps : Nat
  label     : Nat
  deriving Repr, DecidableEq, Inhabited

namespace MessageInfo

/-- Maximum message length in registers (matches seL4 seL4_MsgMaxLength). -/
def maxLength : Nat := maxMessageRegisters

/-- Maximum extra capabilities per message (matches seL4 seL4_MsgMaxExtraCaps). -/
def maxExtraCaps' : Nat := maxExtraCaps

/-- Encode a MessageInfo into a single register word.
    Bit layout (seL4 convention):
    - bits  0..6  : length (7 bits, max 120)
    - bits  7..8  : extraCaps (2 bits, max 3)
    - bits  9..31 : label (23 bits)
    This is a simplified model; real seL4 uses different bit widths. -/
@[inline] def encode (mi : MessageInfo) : Nat :=
  mi.length ||| (mi.extraCaps <<< 7) ||| (mi.label <<< 9)

/-- Decode a raw word into MessageInfo fields by extracting bit fields.
    Returns `none` if the length or extraCaps fields exceed their bounds. -/
@[inline] def decode (w : Nat) : Option MessageInfo :=
  let length    := w &&& 0x7F          -- bits 0..6
  let extraCaps := (w >>> 7) &&& 0x3   -- bits 7..8
  let label     := w >>> 9             -- bits 9+
  if length ≤ maxMessageRegisters && extraCaps ≤ Model.maxExtraCaps then
    some { length, extraCaps, label }
  else
    none

instance : ToString MessageInfo where
  toString mi := s!"MessageInfo(len={mi.length}, caps={mi.extraCaps}, label={mi.label})"

-- ============================================================================
-- Encode/decode round-trip proof (bitwise extraction lemmas)
-- ============================================================================

/-- Bitwise extraction: AND with 0x7F (127) recovers the low 7-bit field
    when the field value fits in 7 bits. -/
private theorem and_mask_127 (a b c : Nat) (ha : a < 128) :
    (a ||| (b <<< 7) ||| (c <<< 9)) &&& 0x7F = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < 7
  · have h7 : ¬(7 ≤ i) := by omega
    have h9 : ¬(9 ≤ i) := by omega
    simp only [h7, h9, decide_false, Bool.false_and, Bool.or_false]
    have hmask : (127 : Nat).testBit i = true := by
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide
    rw [hmask, Bool.and_true]
  · have hmask : (127 : Nat).testBit i = false := by
      apply Nat.testBit_lt_two_pow
      calc (127 : Nat) < 2 ^ 7 := by decide
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [hmask, Bool.and_false]
    symm; apply Nat.testBit_lt_two_pow
    calc a < 128 := ha
      _ = 2 ^ 7 := by decide
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)

/-- Bitwise extraction: shift right 7 then AND with 0x3 recovers the 2-bit
    extraCaps field from position [7..8]. -/
private theorem shift7_and_mask_3 (a b c : Nat) (ha : a < 128) (hb : b < 4) :
    ((a ||| (b <<< 7) ||| (c <<< 9)) >>> 7) &&& 0x3 = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < 2
  · have h7 : 7 ≤ 7 + i := by omega
    have h9 : ¬(9 ≤ 7 + i) := by omega
    simp only [h7, h9, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.or_false]
    have ha_bit : a.testBit (7 + i) = false := by
      apply Nat.testBit_lt_two_pow
      calc a < 128 := ha
        _ = 2 ^ 7 := by decide
        _ ≤ 2 ^ (7 + i) := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [ha_bit, Bool.false_or]
    have : (7 + i) - 7 = i := by omega
    rw [this]
    have hmask : (3 : Nat).testBit i = true := by
      have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl <;> native_decide
    rw [hmask, Bool.and_true]
  · have hmask : (3 : Nat).testBit i = false := by
      apply Nat.testBit_lt_two_pow
      calc (3 : Nat) < 2 ^ 2 := by decide
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [hmask, Bool.and_false]
    symm; apply Nat.testBit_lt_two_pow
    calc b < 4 := hb
      _ = 2 ^ 2 := by decide
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)

/-- Bitwise extraction: shift right 9 recovers the label field from position [9..]. -/
private theorem shift9_extracts_label (a b c : Nat) (ha : a < 128) (hb : b < 4) :
    (a ||| (b <<< 7) ||| (c <<< 9)) >>> 9 = c := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
  have h9 : 9 ≤ 9 + i := by omega
  have h7 : 7 ≤ 9 + i := by omega
  simp only [h9, h7, decide_true, Bool.true_and]
  have ha_bit : a.testBit (9 + i) = false := by
    apply Nat.testBit_lt_two_pow
    calc a < 128 := ha
      _ = 2 ^ 7 := by decide
      _ ≤ 2 ^ (9 + i) := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [ha_bit, Bool.false_or]
  have hb_bit : b.testBit ((9 + i) - 7) = false := by
    have : (9 + i) - 7 = i + 2 := by omega
    rw [this]
    apply Nat.testBit_lt_two_pow
    calc b < 4 := hb
      _ = 2 ^ 2 := by decide
      _ ≤ 2 ^ (i + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [hb_bit, Bool.false_or]
  have : (9 + i) - 9 = i := by omega
  rw [this]

/-- Round-trip: encoding then decoding a MessageInfo recovers the original,
    provided the fields satisfy the seL4 message-info bounds.
    This completes the round-trip proof surface for all three register decode
    components (CPtr, SyscallId, and MessageInfo). -/
theorem encode_decode_roundtrip (mi : MessageInfo)
    (hLen : mi.length ≤ maxMessageRegisters)
    (hCaps : mi.extraCaps ≤ maxExtraCaps) :
    MessageInfo.decode (MessageInfo.encode mi) = some mi := by
  unfold encode decode
  have hLen128 : mi.length < 128 := by unfold maxMessageRegisters at hLen; omega
  have hCaps4 : mi.extraCaps < 4 := by unfold maxExtraCaps at hCaps; omega
  rw [and_mask_127 mi.length mi.extraCaps mi.label hLen128]
  rw [shift7_and_mask_3 mi.length mi.extraCaps mi.label hLen128 hCaps4]
  rw [shift9_extracts_label mi.length mi.extraCaps mi.label hLen128 hCaps4]
  simp only [maxMessageRegisters, maxExtraCaps]
  have : mi.length ≤ 120 ∧ mi.extraCaps ≤ 3 := ⟨hLen, hCaps⟩
  simp [this.1, this.2]

end MessageInfo

/-- Result of decoding raw register values into typed syscall arguments.
    Produced by the register decode layer; consumed by syscall dispatch.
    The `msgRegs` field carries raw values from the layout's message registers
    (x2–x5 on ARM64). Default `#[]` ensures backward compatibility with
    existing construction sites. Per-syscall argument decode (WS-K-B) extracts
    typed arguments from this array. -/
structure SyscallDecodeResult where
  capAddr   : SeLe4n.CPtr
  msgInfo   : MessageInfo
  syscallId : SyscallId
  msgRegs   : Array SeLe4n.RegValue := #[]
  deriving Repr, DecidableEq
