/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Machine

namespace SeLe4n.Model


/-- High-level service runtime status for orchestration-level reasoning. -/
inductive ServiceStatus where
  | stopped
  | running
  | failed
  | isolated
  deriving Repr, DecidableEq

/-- Stable service identity metadata for graph-level orchestration. -/
structure ServiceIdentity where
  sid : ServiceId
  backingObject : SeLe4n.ObjId
  owner : SeLe4n.ObjId
  deriving Repr, DecidableEq

/-- Declared service dependencies and isolation edges. -/
structure ServiceGraphEntry where
  identity : ServiceIdentity
  status : ServiceStatus
  dependencies : List ServiceId
  isolatedFrom : List ServiceId
  deriving Repr, DecidableEq

inductive AccessRight where
  | read
  | write
  | grant
  | grantReply
  deriving Repr, DecidableEq

/-- The addressable target of a capability in the abstract object universe.

WS-E4/M-12: Added `replyCap` variant for one-shot reply capabilities that
reference a specific sender's TCB, enabling bidirectional IPC. -/
inductive CapTarget where
  | object (id : SeLe4n.ObjId)
  | cnodeSlot (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot)
  | replyCap (senderTcb : SeLe4n.ThreadId)
  deriving Repr, DecidableEq

structure Capability where
  target : CapTarget
  rights : List AccessRight
  badge : Option SeLe4n.Badge := none
  deriving Repr, DecidableEq

namespace Capability

def hasRight (cap : Capability) (right : AccessRight) : Bool :=
  right ∈ cap.rights

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
  registers : Array Nat
  caps : Array Capability := #[]
  badge : Option SeLe4n.Badge := none
  deriving Repr, DecidableEq

namespace IpcMessage

def empty : IpcMessage := { registers := #[], caps := #[], badge := none }

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
    a.registerContext == b.registerContext

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

`active` stores a single pending badge, while `waiting` tracks blocked receivers. -/
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

`slots` is backed by `Std.HashMap Slot Capability` for O(1) amortized
lookup, insert, and delete. HashMap key uniqueness is structural. -/
structure CNode where
  depth      : Nat          -- maximum remaining depth in bits from this node to any leaf
  guardWidth : Nat          -- width of guard field in bits
  guardValue : Nat          -- expected guard value to match
  radixWidth : Nat          -- width of slot index in bits (2^radixWidth slots)
  slots      : Std.HashMap SeLe4n.Slot Capability
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
    the byte offset of the new allocation. -/
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
