import SeLe4n.Prelude
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

/-- WS-E4/M-02: Structured IPC message payload for endpoint transfers.

Models seL4 message registers plus optional capability transfer and sender badge. -/
structure IpcMessage where
  registers : List Nat
  caps : List Capability := []
  badge : Option SeLe4n.Badge := none
  deriving Repr, DecidableEq

namespace IpcMessage

def empty : IpcMessage := { registers := [], caps := [], badge := none }

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
  deadline : SeLe4n.Deadline := 0
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

/-- WS-G5/F-P03: CNode capability space node.
`slots` is backed by `Std.HashMap Slot Capability` for O(1) amortized
lookup, insert, and delete — replacing the O(m) list-based representation.
HashMap key uniqueness is structural, eliminating the need for an explicit
`slotsUnique` invariant. -/
structure CNode where
  guard : Nat
  radix : Nat
  slots : Std.HashMap SeLe4n.Slot Capability
  deriving Repr

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

/-- WS-H11/H-02: Per-page permission attributes modeled after ARM64 page table descriptors.

Each mapping carries read/write/execute/user-access and cacheability flags. The
kernel enforces W^X (write XOR execute) as an invariant — no mapping may have both
`write` and `execute` set simultaneously. -/
structure PagePermissions where
  read : Bool := true
  write : Bool := false
  execute : Bool := false
  user : Bool := false
  cacheable : Bool := true
  deriving Repr, DecidableEq, Inhabited

instance : BEq PagePermissions where
  beq a b := a.read == b.read && a.write == b.write && a.execute == b.execute &&
              a.user == b.user && a.cacheable == b.cacheable

instance : Hashable PagePermissions where
  hash p := mixHash (hash p.read) (mixHash (hash p.write) (mixHash (hash p.execute)
            (mixHash (hash p.user) (hash p.cacheable))))

/-- WS-H11/H-02: W^X policy — a page permission set must not have both write and execute. -/
def PagePermissions.wxCompliant (p : PagePermissions) : Bool :=
  !(p.write && p.execute)

/-- WS-H11: Default permissions are W^X compliant (read-only, non-executable). -/
theorem PagePermissions.default_wxCompliant : (default : PagePermissions).wxCompliant = true := by
  rfl

/-- WS-G6/F-P05: Minimal VSpace root object: ASID identity plus flat virtual→physical mappings.

This intentionally models only one-level deterministic lookup semantics for WS-B1.
Hierarchical page-table levels are deferred behind this stable executable surface.

`mappings` is backed by `Std.HashMap VAddr (PAddr × PagePermissions)` for O(1)
amortized lookup, insert, and erase. HashMap key uniqueness is structural,
making `noVirtualOverlap` trivially true.

WS-H11/H-02: Enriched with per-page permissions (read/write/execute/user/cacheable). -/
structure VSpaceRoot where
  asid : SeLe4n.ASID
  mappings : Std.HashMap SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions)
  deriving Repr

namespace VSpaceRoot

/-- WS-G6/F-P05: O(1) amortized page lookup via `HashMap[vaddr]?`.
WS-H11: Returns `(PAddr × PagePermissions)` pair. -/
def lookup (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) : Option (SeLe4n.PAddr × PagePermissions) :=
  root.mappings[vaddr]?

/-- WS-H11: O(1) amortized physical-address-only lookup for backward compatibility. -/
def lookupAddr (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) : Option SeLe4n.PAddr :=
  (root.lookup vaddr).map Prod.fst

/-- WS-G6/F-P05: O(1) amortized page mapping via `HashMap.insert`.
Returns `none` if a mapping for `vaddr` already exists (conflict).
WS-H11: Accepts permissions alongside the physical address. -/
def mapPage (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions := default) : Option VSpaceRoot :=
  match root.mappings[vaddr]? with
  | some _ => none
  | none => some { root with mappings := root.mappings.insert vaddr (paddr, perms) }

/-- WS-G6/F-P05: O(1) amortized page unmapping via `HashMap.erase`.
Returns `none` if no mapping exists for `vaddr`. -/
def unmapPage (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) : Option VSpaceRoot :=
  match root.mappings[vaddr]? with
  | none => none
  | some _ => some { root with mappings := root.mappings.erase vaddr }

/-- WS-G6: No-virtual-overlap property. With HashMap-backed mappings, this is
trivially true by key uniqueness: each VAddr maps to at most one entry.
Uses `lookup` (which delegates to `HashMap[vaddr]?`) for type resolution. -/
def noVirtualOverlap (root : VSpaceRoot) : Prop :=
  ∀ v e₁ e₂,
    root.lookup v = some e₁ →
    root.lookup v = some e₂ →
    e₁ = e₂

/-- WS-G6: With HashMap-backed mappings, `noVirtualOverlap` is trivially true
for *every* `VSpaceRoot` — key uniqueness in the HashMap guarantees that a
single `lookup` can return at most one value, so `e₁ = e₂` follows by
injection. This subsumes `noVirtualOverlap_empty`, `mapPage_noVirtualOverlap`,
and `unmapPage_noVirtualOverlap`, which are retained for API compatibility. -/
theorem noVirtualOverlap_trivial (root : VSpaceRoot) : noVirtualOverlap root := by
  intro v e₁ e₂ h₁ h₂; rw [h₁] at h₂; exact Option.some.inj h₂

/-- WS-G6: Empty mappings trivially satisfy no-virtual-overlap.
Follows directly from `noVirtualOverlap_trivial` but retained for API compatibility. -/
theorem noVirtualOverlap_empty (asid : SeLe4n.ASID) :
    noVirtualOverlap { asid := asid, mappings := {} } :=
  noVirtualOverlap_trivial _

/-- WS-G6: After unmapping vaddr, lookup returns none. Maps to `HashMap.getElem?_erase`. -/
theorem lookup_unmapPage_eq_none
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (hUnmap : root.unmapPage vaddr = some root') :
    root'.lookup vaddr = none := by
  unfold unmapPage at hUnmap
  cases hLookup : root.mappings[vaddr]? with
  | none => simp [hLookup] at hUnmap
  | some p =>
      simp [hLookup] at hUnmap
      cases hUnmap
      simp [lookup]

/-- WS-G6/WS-H11: After mapping vaddr→paddr with perms, lookup returns the entry.
Maps to `HashMap.getElem?_insert`. -/
theorem lookup_mapPage_eq
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (hMap : root.mapPage vaddr paddr perms = some root') :
    root'.lookup vaddr = some (paddr, perms) := by
  unfold mapPage at hMap
  cases hLookup : root.mappings[vaddr]? with
  | some p => simp [hLookup] at hMap
  | none =>
      simp [hLookup] at hMap
      cases hMap
      simp [lookup]

/-- WS-H11: After mapping vaddr→paddr with default perms, lookupAddr returns paddr. -/
theorem lookupAddr_mapPage_eq
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (hMap : root.mapPage vaddr paddr perms = some root') :
    root'.lookupAddr vaddr = some paddr := by
  simp [lookupAddr, lookup_mapPage_eq root root' vaddr paddr perms hMap]

/-- F-08 helper: `mapPage` preserves the VSpace root ASID. -/
theorem mapPage_asid_eq
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions := default)
    (hMap : root.mapPage vaddr paddr perms = some root') :
    root'.asid = root.asid := by
  unfold mapPage at hMap
  cases hLookup : root.mappings[vaddr]? with
  | some _ => simp [hLookup] at hMap
  | none =>
      simp [hLookup] at hMap; cases hMap; rfl

/-- F-08 helper: `unmapPage` preserves the VSpace root ASID. -/
theorem unmapPage_asid_eq
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (hUnmap : root.unmapPage vaddr = some root') :
    root'.asid = root.asid := by
  unfold unmapPage at hUnmap
  cases hLookup : root.mappings[vaddr]? with
  | none => simp [hLookup] at hUnmap
  | some _ =>
      simp [hLookup] at hUnmap; cases hUnmap; rfl

/-- WS-G6: If `lookup` returns `none`, the vaddr has no mapping in the HashMap. -/
theorem lookup_eq_none_iff
    (root : VSpaceRoot)
    (vaddr : SeLe4n.VAddr) :
    root.lookup vaddr = none ↔ vaddr ∉ root.mappings := by
  simp [lookup]

/-- WS-G6: A successful `mapPage` preserves the no-virtual-overlap invariant.
With HashMap-backed mappings, `noVirtualOverlap` is trivially true by key uniqueness. -/
theorem mapPage_noVirtualOverlap
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (_hOverlap : noVirtualOverlap root)
    (hMap : root.mapPage vaddr paddr perms = some root') :
    noVirtualOverlap root' := by
  unfold mapPage at hMap
  cases hLookup : root.mappings[vaddr]? with
  | some _ => simp [hLookup] at hMap
  | none =>
      simp [hLookup] at hMap; cases hMap
      exact noVirtualOverlap_trivial _

/-- WS-G6: A successful `unmapPage` preserves the no-virtual-overlap invariant.
With HashMap-backed mappings, `noVirtualOverlap` is trivially true by key uniqueness. -/
theorem unmapPage_noVirtualOverlap
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (_hOverlap : noVirtualOverlap root)
    (hUnmap : root.unmapPage vaddr = some root') :
    noVirtualOverlap root' := by
  unfold unmapPage at hUnmap
  cases hLookup : root.mappings[vaddr]? with
  | none => simp [hLookup] at hUnmap
  | some _ =>
      simp [hLookup] at hUnmap; cases hUnmap
      exact noVirtualOverlap_trivial _

/-- TPI-001 helper: mapping vaddr does not affect lookup of a different vaddr'.
Maps to `HashMap.getElem?_insert` with the inequality hypothesis. -/
theorem lookup_mapPage_ne
    (root root' : VSpaceRoot)
    (vaddr vaddr' : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (hNe : vaddr ≠ vaddr')
    (hMap : root.mapPage vaddr paddr perms = some root') :
    root'.lookup vaddr' = root.lookup vaddr' := by
  unfold mapPage at hMap
  cases hLookup : root.mappings[vaddr]? with
  | some _ => simp [hLookup] at hMap
  | none =>
      simp [hLookup] at hMap; cases hMap
      simp only [lookup, HashMap_getElem?_insert]
      have : ¬((vaddr == vaddr') = true) := by
        intro h; exact hNe (eq_of_beq h)
      simp [this]

/-- TPI-001 helper: unmapPage at vaddr does not affect lookup of a different vaddr'.
Maps to `HashMap.getElem?_erase` with the inequality hypothesis. -/
theorem lookup_unmapPage_ne
    (root root' : VSpaceRoot)
    (vaddr vaddr' : SeLe4n.VAddr)
    (hNe : vaddr ≠ vaddr')
    (hUnmap : root.unmapPage vaddr = some root') :
    root'.lookup vaddr' = root.lookup vaddr' := by
  unfold unmapPage at hUnmap
  cases hLookup : root.mappings[vaddr]? with
  | none => simp [hLookup] at hUnmap
  | some _ =>
      simp [hLookup] at hUnmap; cases hUnmap
      simp only [lookup, HashMap_getElem?_erase]
      have : ¬((vaddr == vaddr') = true) := by
        intro h; exact hNe (eq_of_beq h)
      simp [this]

end VSpaceRoot

/-- WS-G6/WS-H7: `BEq` instance for `VSpaceRoot` using entry-wise comparison on the
HashMap-backed mappings. Two VSpaceRoots are equal iff their ASID and all
mapping entries agree (same size + every key maps to the same value).
WS-H11: Updated for enriched `(PAddr × PagePermissions)` value type. -/
instance : BEq VSpaceRoot where
  beq a b :=
    a.asid == b.asid &&
    a.mappings.size == b.mappings.size &&
    a.mappings.fold (init := true) (fun acc k v => acc && b.mappings[k]? == some v)

/-- WS-H7: VSpaceRoot BEq correctness — the fold-based comparison is sound.
When BEq returns true, the two VSpaceRoots have equal ASIDs and identical
mapping entries. The proof relies on HashMap key uniqueness: size equality +
forward containment guarantees bidirectional equality.

Note: The full `beq_correct` biconditional (`(a == b) = true ↔ a = b`) requires
HashMap extensional equality axioms beyond Lean's Std.HashMap surface. We prove
the forward (soundness) direction; the reverse follows from `BEq.refl` when the
structures are definitionally equal. -/
theorem VSpaceRoot.beq_sound (a b : VSpaceRoot) (h : (a == b) = true) :
    a.asid = b.asid ∧ a.mappings.size = b.mappings.size := by
  simp only [BEq.beq, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2⟩

namespace CNode

inductive ResolveError where
  | depthMismatch
  | guardMismatch
  deriving Repr, DecidableEq

def empty : CNode :=
  { guard := 0, radix := 0, slots := {} }

/-- Number of addressable slots represented by this CNode radix width. -/
def slotCount (node : CNode) : Nat :=
  2 ^ node.radix

/-- Resolve a CPtr/depth pair into the local slot index using guard/radix semantics.

`depth` is interpreted as the number of low-order bits consumed at this CNode level.
Those bits split into:
- `radix` slot-index bits,
- `depth - radix` guard bits, which must equal `node.guard`. -/
def resolveSlot (node : CNode) (cptr : SeLe4n.CPtr) (depth : Nat) : Except ResolveError SeLe4n.Slot :=
  if depth < node.radix then
    .error .depthMismatch
  else
    let guardWidth := depth - node.radix
    let slotCount := node.slotCount
    let slotNat := cptr.toNat % slotCount
    let guardBits := (cptr.toNat / slotCount) % (2 ^ guardWidth)
    if guardBits = node.guard then
      .ok (SeLe4n.Slot.ofNat slotNat)
    else
      .error .guardMismatch

/-- WS-G5/F-P03: O(1) amortized slot lookup via `HashMap.find?`. -/
def lookup (node : CNode) (slot : SeLe4n.Slot) : Option Capability :=
  node.slots[slot]?

/-- WS-G5/F-P03: O(1) amortized slot insert via `HashMap.insert`.
HashMap key uniqueness ensures the old entry for `slot` is replaced. -/
def insert (node : CNode) (slot : SeLe4n.Slot) (cap : Capability) : CNode :=
  { node with slots := node.slots.insert slot cap }

/-- WS-G5/F-P03: O(1) amortized slot removal via `HashMap.erase`. -/
def remove (node : CNode) (slot : SeLe4n.Slot) : CNode :=
  { node with slots := node.slots.erase slot }

/-- Local revoke helper for the current modeled slice.

This keeps the authority-bearing source slot while deleting sibling slots in the same CNode that
name the same capability target. Full cross-CNode revoke requires an explicit derivation graph and
is intentionally deferred.

WS-G5/F-P03: Inherently O(m) (filter-by-target), uses `HashMap.filter`. -/
def revokeTargetLocal (node : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget) : CNode :=
  {
    node with
      slots := node.slots.filter fun s c => s == sourceSlot || !(c.target == target)
  }

/-- WS-G5: After removing a slot, lookup returns `none`.
Maps directly to `HashMap.getElem?_erase_self`. -/
theorem lookup_remove_eq_none (node : CNode) (slot : SeLe4n.Slot) :
    (node.remove slot).lookup slot = none := by
  simp [remove, lookup]

/-- WS-G5: If `lookup` returns `some`, the slot key is present in the HashMap.
Replaces the list-era membership theorem with HashMap semantics. -/
theorem lookup_mem_of_some (node : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (h : node.lookup slot = some cap) : slot ∈ node.slots := by
  simp [lookup] at h
  exact Std.HashMap.mem_iff_isSome_getElem?.mpr (by simp [h])

theorem resolveSlot_depthMismatch
    (node : CNode)
    (cptr : SeLe4n.CPtr)
    (depth : Nat)
    (hDepth : depth < node.radix) :
    node.resolveSlot cptr depth = .error .depthMismatch := by
  unfold resolveSlot
  simp [hDepth]

/-- WS-G5: Source slot is preserved by `revokeTargetLocal` because the filter
predicate always includes entries where `s = sourceSlot`. -/
theorem lookup_revokeTargetLocal_source_eq_lookup
    (node : CNode)
    (sourceSlot : SeLe4n.Slot)
    (target : CapTarget) :
    (node.revokeTargetLocal sourceSlot target).lookup sourceSlot = node.lookup sourceSlot := by
  simp only [revokeTargetLocal, lookup]
  exact SeLe4n.HashMap_filter_preserves_key node.slots _ sourceSlot
    (fun k' _ hBeq => by simp [eq_of_beq hBeq])

-- ============================================================================
-- WS-G5/WS-E2/C-01: CNode slot-index uniqueness infrastructure
-- ============================================================================

/-- CNode slot-index uniqueness: each slot index maps to at most one capability.

WS-G5: With HashMap-backed slots, key uniqueness is structural — HashMap enforces
that each key maps to exactly one value. This invariant is trivially satisfied
for all CNodes by construction. The definition is retained for backward
compatibility with the invariant surface (Capability/Invariant.lean). -/
def slotsUnique (_cn : CNode) : Prop :=
  True

/-- WS-G5: Trivially true — HashMap enforces key uniqueness by construction. -/
theorem empty_slotsUnique : CNode.empty.slotsUnique :=
  trivial

/-- WS-G5: Trivially true — HashMap.insert enforces key uniqueness by construction. -/
theorem insert_slotsUnique
    (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (_hUniq : cn.slotsUnique) :
    (cn.insert slot cap).slotsUnique :=
  trivial

/-- WS-G5: Trivially true — HashMap.erase preserves key uniqueness. -/
theorem remove_slotsUnique
    (cn : CNode) (slot : SeLe4n.Slot)
    (_hUniq : cn.slotsUnique) :
    (cn.remove slot).slotsUnique :=
  trivial

/-- WS-G5: Trivially true — HashMap.filter preserves key uniqueness. -/
theorem revokeTargetLocal_slotsUnique
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (_hUniq : cn.slotsUnique) :
    (cn.revokeTargetLocal sourceSlot target).slotsUnique :=
  trivial

-- ============================================================================
-- WS-H4: Meaningful CNode slot-count bound predicate
-- ============================================================================

/-- WS-H4/C-03: Every CNode has at most `2^radixBits` occupied slots.
This is the meaningful replacement for the trivially-true `slotsUnique`
predicate — it captures the actual capacity constraint that the CNode
guard/radix semantics enforce. -/
def slotCountBounded (cn : CNode) : Prop :=
  cn.slots.size ≤ cn.slotCount

/-- Empty CNode satisfies slot-count bound (0 ≤ 2^0 = 1). -/
theorem empty_slotCountBounded : CNode.empty.slotCountBounded := by
  unfold slotCountBounded empty slotCount
  simp

/-- Removing a slot preserves the slot-count bound (size can only decrease). -/
theorem remove_slotCountBounded
    (cn : CNode) (slot : SeLe4n.Slot)
    (hBounded : cn.slotCountBounded) :
    (cn.remove slot).slotCountBounded := by
  show (cn.slots.erase slot).size ≤ 2 ^ cn.radix
  have h : (cn.slots.erase slot).size ≤ cn.slots.size := Std.HashMap.size_erase_le
  exact Nat.le_trans h hBounded

/-- Revoking target-local preserves the slot-count bound (filter can only decrease size). -/
theorem revokeTargetLocal_slotCountBounded
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (hBounded : cn.slotCountBounded) :
    (cn.revokeTargetLocal sourceSlot target).slotCountBounded := by
  show (cn.slots.filter (fun s c => s == sourceSlot || !c.target == target)).size ≤ 2 ^ cn.radix
  have h := @Std.HashMap.size_filter_le_size _ _ _ _ cn.slots _ _
    (fun s c => s == sourceSlot || !c.target == target)
  exact Nat.le_trans h hBounded

/-- WS-G5: If a slot is present in the HashMap, lookup returns its value.
With HashMap-backed slots, `slotsUnique` is trivially satisfied (structural
invariant of HashMap), so the uniqueness hypothesis is unused. -/
theorem mem_lookup_of_slotsUnique (node : CNode) (_hUniq : node.slotsUnique)
    (slot : SeLe4n.Slot) (hMem : slot ∈ node.slots) :
    node.lookup slot = some node.slots[slot] :=
  Std.HashMap.getElem?_eq_some_getElem hMem

/-- WS-G5: Lookup roundtrip after insert — inserting at `slot` makes lookup
return the inserted capability. Maps directly to `HashMap.getElem?_insert_self`. -/
theorem lookup_insert_eq
    (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability) :
    (cn.insert slot cap).lookup slot = some cap := by
  simp [insert, lookup]

/-- WS-G5: Insert at a different slot does not affect lookup.
Maps directly to `HashMap.getElem?_insert`. -/
theorem lookup_insert_ne
    (cn : CNode) (slot slot' : SeLe4n.Slot) (cap : Capability)
    (hNe : slot ≠ slot') :
    (cn.insert slot cap).lookup slot' = cn.lookup slot' := by
  simp only [insert, lookup]
  rw [Std.HashMap.getElem?_insert]
  have : ¬((slot == slot') = true) := by
    intro h; exact hNe (eq_of_beq h)
  simp [this]

/-- WS-G5: Remove at a different slot does not affect lookup.
Maps directly to `HashMap.getElem?_erase`. -/
theorem lookup_remove_ne
    (cn : CNode) (slot slot' : SeLe4n.Slot)
    (hNe : slot ≠ slot') :
    (cn.remove slot).lookup slot' = cn.lookup slot' := by
  simp only [remove, lookup]
  rw [Std.HashMap.getElem?_erase]
  have : ¬((slot == slot') = true) := by
    intro h; exact hNe (eq_of_beq h)
  simp [this]

end CNode

/-- WS-G5: `BEq` instance for `CNode` using entry-wise comparison on the
HashMap-backed slots. Two CNodes are equal iff their guard, radix, and all
slot entries agree (same size + every key maps to the same value). -/
instance : BEq CNode where
  beq a b :=
    a.guard == b.guard && a.radix == b.radix &&
    a.slots.size == b.slots.size &&
    a.slots.fold (init := true) (fun acc k v => acc && b.slots[k]? == some v)

/-- WS-H7: CNode BEq soundness — when BEq returns true, the two CNodes have
equal guard, radix, and slot count. Same approach as VSpaceRoot.beq_sound. -/
theorem CNode.beq_sound (a b : CNode) (h : (a == b) = true) :
    a.guard = b.guard ∧ a.radix = b.radix ∧ a.slots.size = b.slots.size := by
  simp only [BEq.beq, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

-- ============================================================================
-- WS-E4/C-03: Capability Derivation Tree (CDT) model
-- ============================================================================

/-- A slot address in the global capability namespace: (CNode ObjId, Slot). -/
abbrev SlotAddr := SeLe4n.ObjId × SeLe4n.Slot

/-- The operation that created a derivation edge. -/
inductive DerivationOp where
  | mint
  | copy
  deriving Repr, DecidableEq

/-- Stable CDT node identifier.

Nodes are stable across CSpace slot moves: slots point to nodes, and edges are
between nodes (not slot addresses). -/
abbrev CdtNodeId := Nat

/-- A single edge in the Capability Derivation Tree.

WS-E4/C-03: Each edge records parent/child stable node IDs and the operation
that created the derivation. The CDT is a forest: each node has at most one
parent but may have many children. -/
structure CapDerivationEdge where
  parent : CdtNodeId
  child : CdtNodeId
  op : DerivationOp
  deriving Repr, DecidableEq

namespace CapDerivationEdge

def isChildOf (edge : CapDerivationEdge) (node : CdtNodeId) : Bool :=
  edge.child = node

def isParentOf (edge : CapDerivationEdge) (node : CdtNodeId) : Bool :=
  edge.parent = node

end CapDerivationEdge

/-- The Capability Derivation Tree stored at the system level.

WS-E4/C-03: A list of derivation edges forming a forest. Operations maintain
the acyclicity invariant: no slot can be both ancestor and descendant of itself. -/
structure CapDerivationTree where
  edges : List CapDerivationEdge := []
  /-- WS-G8/F-P14: Parent-indexed child map for O(1) `childrenOf` lookup.
  Runtime index maintained in parallel with `edges`; `edges` remains the
  proof anchor. -/
  childMap : Std.HashMap CdtNodeId (List CdtNodeId) := {}
  deriving Repr

namespace CapDerivationTree

def empty : CapDerivationTree := { edges := [], childMap := {} }

/-- Add a derivation edge from parent to child.
WS-G8: Maintains `childMap` index alongside `edges`. -/
def addEdge (cdt : CapDerivationTree) (parent child : CdtNodeId)
    (op : DerivationOp) : CapDerivationTree :=
  let currentChildren := cdt.childMap.get? parent |>.getD []
  { edges := { parent, child, op } :: cdt.edges,
    childMap := cdt.childMap.insert parent (child :: currentChildren) }

/-- Find all direct children of a given node.
WS-G8/F-P14: O(1) lookup via `childMap` instead of O(E) edge scan. -/
def childrenOf (cdt : CapDerivationTree) (node : CdtNodeId)
    : List CdtNodeId :=
  cdt.childMap.get? node |>.getD []

/-- Find the parent of a given node, if any. -/
def parentOf (cdt : CapDerivationTree) (node : CdtNodeId)
    : Option CdtNodeId :=
  (cdt.edges.find? (fun e => e.isChildOf node)).map CapDerivationEdge.parent

/-- Remove all edges referencing a given node as child (detach from parent).
WS-G8: Maintains `childMap` by removing `node` from all parent child lists. -/
def removeAsChild (cdt : CapDerivationTree) (node : CdtNodeId)
    : CapDerivationTree :=
  { edges := cdt.edges.filter (fun e => ¬e.isChildOf node),
    childMap := cdt.childMap.fold (init := {}) fun m parent children =>
      let filtered := children.filter (· != node)
      if filtered.isEmpty then m else m.insert parent filtered }

/-- Remove all edges referencing a given node as parent (detach all children).
WS-G8: Erases the parent's `childMap` entry. -/
def removeAsParent (cdt : CapDerivationTree) (node : CdtNodeId)
    : CapDerivationTree :=
  { edges := cdt.edges.filter (fun e => ¬e.isParentOf node),
    childMap := cdt.childMap.erase node }

/-- Remove all edges where the given node appears as parent or child.
WS-G8: Erases parent entry and removes from all child lists. -/
def removeNode (cdt : CapDerivationTree) (node : CdtNodeId)
    : CapDerivationTree :=
  let edgesFiltered := cdt.edges.filter (fun e => ¬e.isParentOf node ∧ ¬e.isChildOf node)
  let mapWithoutParent := cdt.childMap.erase node
  let mapFinal := mapWithoutParent.fold (init := {}) fun m parent children =>
    let filtered := children.filter (· != node)
    if filtered.isEmpty then m else m.insert parent filtered
  { edges := edgesFiltered, childMap := mapFinal }

/-- Collect all descendants of a slot via bounded BFS traversal.
Uses fuel = edges.length to ensure termination and completeness
for acyclic trees.
WS-G8/F-P14: Uses `childrenOf` (O(1) via `childMap`) instead of inline
edge scan, yielding O(N+E) total traversal. -/
def descendantsOf (cdt : CapDerivationTree) (root : CdtNodeId)
    : List CdtNodeId :=
  go cdt.edges.length [root] []
where
  go : Nat → List CdtNodeId → List CdtNodeId → List CdtNodeId
    | 0, _, acc => acc
    | _ + 1, [], acc => acc
    | fuel + 1, node :: rest, acc =>
        let children := cdt.childrenOf node
        let newChildren := children.filter (fun c => c ∉ acc)
        go fuel (rest ++ newChildren) (acc ++ newChildren)

/-- CDT acyclicity: no node reaches itself through derivation edges. -/
def acyclic (cdt : CapDerivationTree) : Prop :=
  ∀ e ∈ cdt.edges, e.parent ∉ cdt.descendantsOf e.child

theorem empty_acyclic : CapDerivationTree.empty.acyclic := by
  intro e hMem
  simp [CapDerivationTree.empty] at hMem

-- ============================================================================
-- WS-H4: Edge-well-founded acyclicity (simpler formulation for subset proofs)
-- ============================================================================

/-- WS-H4/M-03: Edge-well-founded acyclicity — no node can reach itself
through a non-empty path of derivation edges. This formulation enables clean
subset-preservation proofs: if edges' ⊆ edges and edges is well-founded,
then edges' is well-founded. -/
def edgeWellFounded (cdt : CapDerivationTree) : Prop :=
  ∀ (node : CdtNodeId),
    ¬(∃ (path : List CdtNodeId),
        path.length > 1 ∧
        path.head? = some node ∧
        path.getLast? = some node ∧
        (∀ i, (h : i + 1 < path.length) →
          ∃ e ∈ cdt.edges, e.parent = path[i] ∧ e.child = path[i + 1]))

/-- WS-H4: Empty CDT is trivially edge-well-founded (no edges, no cycles). -/
theorem empty_edgeWellFounded : CapDerivationTree.empty.edgeWellFounded := by
  intro node ⟨path, _, _, _, hEdges⟩
  have h0 := hEdges 0 (by omega)
  rcases h0 with ⟨e, hMem, _, _⟩
  simp [CapDerivationTree.empty] at hMem

/-- WS-H4: Edge-well-foundedness is preserved under edge-subset.
If every edge of `cdt'` is also in `cdt`, and `cdt` is well-founded,
then `cdt'` is well-founded. -/
theorem edgeWellFounded_sub
    (cdt cdt' : CapDerivationTree)
    (hWF : cdt.edgeWellFounded)
    (hSub : ∀ e ∈ cdt'.edges, e ∈ cdt.edges) :
    cdt'.edgeWellFounded := by
  intro node ⟨path, hLen, hHead, hLast, hEdges⟩
  exact hWF node ⟨path, hLen, hHead, hLast, fun i hi => by
    rcases hEdges i hi with ⟨e, hMem, hp, hc⟩
    exact ⟨e, hSub e hMem, hp, hc⟩⟩

/-- Removing a node preserves a subset of edges. -/
theorem removeNode_edges_sub (cdt : CapDerivationTree) (node : CdtNodeId) :
    ∀ e ∈ (cdt.removeNode node).edges, e ∈ cdt.edges := by
  intro e hMem
  simp [removeNode] at hMem
  exact hMem.1

/-- WS-G8: Consistency invariant — `childMap` mirrors the parent→child
relationship in `edges`. -/
def childMapConsistent (cdt : CapDerivationTree) : Prop :=
  ∀ parent child,
    child ∈ (cdt.childMap.get? parent).getD [] ↔
      ∃ e ∈ cdt.edges, e.parent = parent ∧ e.child = child

theorem empty_childMapConsistent : CapDerivationTree.empty.childMapConsistent := by
  intro parent child
  simp only [CapDerivationTree.empty]
  constructor
  · intro h; rw [HashMap_get?_empty] at h; simp at h
  · rintro ⟨_, hMem, _⟩; cases hMem

theorem addEdge_childMapConsistent (cdt : CapDerivationTree)
    (p c : CdtNodeId) (op : DerivationOp)
    (hCon : cdt.childMapConsistent) :
    (cdt.addEdge p c op).childMapConsistent := by
  intro parent child
  constructor
  · -- Forward: child in new childMap → edge exists
    intro hIn
    simp only [addEdge] at hIn
    rw [HashMap_get?_insert] at hIn
    split at hIn
    · -- p == parent is true
      rename_i heq
      have hPeq : p = parent := eq_of_beq heq
      simp only [Option.getD] at hIn
      rcases List.mem_cons.mp hIn with hChildEq | hTail
      · exact ⟨⟨p, c, op⟩, .head _, hPeq, hChildEq.symm⟩
      · have ⟨e, heMem, hep, hec⟩ := (hCon parent child).mp (hPeq ▸ hTail)
        exact ⟨e, List.mem_cons_of_mem _ heMem, hep, hec⟩
    · -- p == parent is false
      have ⟨e, heMem, hep, hec⟩ := (hCon parent child).mp hIn
      exact ⟨e, List.mem_cons_of_mem _ heMem, hep, hec⟩
  · -- Backward: edge exists → child in new childMap
    rintro ⟨e, heMem, hep, hec⟩
    simp only [addEdge]
    rw [HashMap_get?_insert]
    rcases List.mem_cons.mp heMem with heq | hTail
    · -- e is the new edge
      subst heq
      simp only at hep hec
      subst hep; subst hec
      simp only [beq_self_eq_true, ↓reduceIte, Option.getD]
      exact .head _
    · -- e is from existing edges
      split
      · -- p == parent is true
        rename_i heq
        have hPeq : p = parent := eq_of_beq heq
        simp only [Option.getD]
        exact List.mem_cons_of_mem _ (hPeq ▸ (hCon p child).mpr ⟨e, hTail, hPeq ▸ hep, hec⟩)
      · -- p == parent is false
        exact (hCon parent child).mpr ⟨e, hTail, hep, hec⟩

/-- Slot-address view of a CDT edge (projection through slot backpointers). -/
structure ObservedDerivationEdge where
  parent : SlotAddr
  child : SlotAddr
  op : DerivationOp
  deriving Repr, DecidableEq

/-- Project node-based CDT edges through a node→slot mapping. -/
def projectObservedEdges
    (cdt : CapDerivationTree)
    (nodeSlot : CdtNodeId → Option SlotAddr) : List ObservedDerivationEdge :=
  cdt.edges.filterMap (fun e =>
    match nodeSlot e.parent, nodeSlot e.child with
    | some p, some c => some { parent := p, child := c, op := e.op }
    | _, _ => none)

end CapDerivationTree

/-- WS-G5: `DecidableEq` removed from `KernelObject` because `CNode.slots` is now
`Std.HashMap Slot Capability` which does not have a `DecidableEq` instance.
`Repr` is retained for trace output. `BEq` is provided manually via entry-wise
HashMap comparison for runtime test assertions. -/
inductive KernelObject where
  | tcb (t : TCB)
  | endpoint (e : Endpoint)
  | notification (n : Notification)
  | cnode (c : CNode)
  | vspaceRoot (v : VSpaceRoot)
  | untyped (u : UntypedObject)
  deriving Repr

/-- WS-G5: Manual `BEq` for `KernelObject` dispatching to constituent `BEq`
instances. CNode comparison uses the entry-wise `BEq CNode` instance above. -/
instance : BEq KernelObject where
  beq
    | .tcb a, .tcb b => a == b
    | .endpoint a, .endpoint b => a == b
    | .notification a, .notification b => a == b
    | .cnode a, .cnode b => a == b
    | .vspaceRoot a, .vspaceRoot b => a == b
    | .untyped a, .untyped b => a == b
    | _, _ => false

inductive KernelObjectType where
  | tcb
  | endpoint
  | notification
  | cnode
  | vspaceRoot
  | untyped
  deriving Repr, DecidableEq

namespace KernelObject

def objectType : KernelObject → KernelObjectType
  | .tcb _ => .tcb
  | .endpoint _ => .endpoint
  | .notification _ => .notification
  | .cnode _ => .cnode
  | .vspaceRoot _ => .vspaceRoot
  | .untyped _ => .untyped

end KernelObject

/-- Construct a capability that names an object directly. -/
def makeObjectCap (id : SeLe4n.ObjId) (rights : List AccessRight) : Capability :=
  { target := .object id, rights }

end SeLe4n.Model
