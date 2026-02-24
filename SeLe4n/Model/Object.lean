import SeLe4n.Prelude

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

/-- The addressable target of a capability in the abstract object universe. -/
inductive CapTarget where
  | object (id : SeLe4n.ObjId)
  | cnodeSlot (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot)
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

/-- Minimal per-thread IPC scheduler-visible status for M3.5 handshake scaffolding.

This is intentionally narrow: only endpoint-local blocking states needed to model one deterministic
waiting-thread handshake story. -/
inductive ThreadIpcState where
  | ready
  | blockedOnSend (endpoint : SeLe4n.ObjId)
  | blockedOnReceive (endpoint : SeLe4n.ObjId)
  | blockedOnNotification (notification : SeLe4n.ObjId)
  deriving Repr, DecidableEq

structure TCB where
  tid : SeLe4n.ThreadId
  priority : SeLe4n.Priority
  domain : SeLe4n.DomainId
  cspaceRoot : SeLe4n.ObjId
  vspaceRoot : SeLe4n.ObjId
  ipcBuffer : SeLe4n.VAddr
  ipcState : ThreadIpcState := .ready
  deriving Repr, DecidableEq

inductive EndpointState where
  | idle
  | send
  | receive
  deriving Repr, DecidableEq

structure Endpoint where
  state : EndpointState
  queue : List SeLe4n.ThreadId
  waitingReceiver : Option SeLe4n.ThreadId := none
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

structure CNode where
  guard : Nat
  radix : Nat
  slots : List (SeLe4n.Slot × Capability)
  deriving Repr, DecidableEq

/-- Minimal VSpace root object: ASID identity plus flat virtual→physical mappings.

This intentionally models only one-level deterministic lookup semantics for WS-B1.
Hierarchical page-table levels are deferred behind this stable executable surface. -/
structure VSpaceRoot where
  asid : SeLe4n.ASID
  mappings : List (SeLe4n.VAddr × SeLe4n.PAddr)
  deriving Repr, DecidableEq

namespace VSpaceRoot

def lookup (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) : Option SeLe4n.PAddr :=
  (root.mappings.find? (fun entry => entry.fst = vaddr)).map Prod.snd

def mapPage (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr) : Option VSpaceRoot :=
  match lookup root vaddr with
  | some _ => none
  | none => some { root with mappings := (vaddr, paddr) :: root.mappings }

def unmapPage (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) : Option VSpaceRoot :=
  match lookup root vaddr with
  | none => none
  | some _ =>
      let mappings' := root.mappings.filter (fun entry => entry.fst ≠ vaddr)
      some { root with mappings := mappings' }

def noVirtualOverlap (root : VSpaceRoot) : Prop :=
  ∀ v p₁ p₂,
    (v, p₁) ∈ root.mappings →
    (v, p₂) ∈ root.mappings →
    p₁ = p₂

theorem noVirtualOverlap_empty (asid : SeLe4n.ASID) :
    noVirtualOverlap { asid := asid, mappings := [] } := by
  intro v p₁ p₂ hIn₁
  simp at hIn₁

theorem lookup_unmapPage_eq_none
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (hUnmap : root.unmapPage vaddr = some root') :
    root'.lookup vaddr = none := by
  unfold unmapPage at hUnmap
  cases hLookup : lookup root vaddr with
  | none => simp [hLookup] at hUnmap
  | some p =>
      simp [hLookup] at hUnmap
      cases hUnmap
      unfold lookup
      simp

theorem lookup_mapPage_eq
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (hMap : root.mapPage vaddr paddr = some root') :
    root'.lookup vaddr = some paddr := by
  unfold mapPage at hMap
  cases hLookup : lookup root vaddr with
  | some p => simp [hLookup] at hMap
  | none =>
      simp [hLookup] at hMap
      cases hMap
      unfold lookup
      simp

/-- F-08 helper: `mapPage` preserves the VSpace root ASID. -/
theorem mapPage_asid_eq
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (hMap : root.mapPage vaddr paddr = some root') :
    root'.asid = root.asid := by
  unfold mapPage at hMap
  cases hLookup : lookup root vaddr with
  | some _ => simp [hLookup] at hMap
  | none => simp [hLookup] at hMap; cases hMap; rfl

/-- F-08 helper: `unmapPage` preserves the VSpace root ASID. -/
theorem unmapPage_asid_eq
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (hUnmap : root.unmapPage vaddr = some root') :
    root'.asid = root.asid := by
  unfold unmapPage at hUnmap
  cases hLookup : lookup root vaddr with
  | none => simp [hLookup] at hUnmap
  | some _ => simp [hLookup] at hUnmap; cases hUnmap; rfl

/-- F-08 helper: if `lookup` returns `none`, then no mapping entry for that vaddr
    exists in the mappings list. -/
theorem lookup_eq_none_not_mem
    (root : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (hNone : lookup root vaddr = none) :
    (vaddr, paddr) ∉ root.mappings := by
  unfold lookup at hNone
  rw [Option.map_eq_none_iff] at hNone
  rw [List.find?_eq_none] at hNone
  intro hMem
  have := hNone ⟨vaddr, paddr⟩ hMem
  simp at this

/-- F-08 helper: a successful `mapPage` preserves the no-virtual-overlap invariant.
    Since `mapPage` only succeeds when `lookup root vaddr = none` (no existing mapping
    for the target vaddr), adding the new `(vaddr, paddr)` entry cannot create duplicates. -/
theorem mapPage_noVirtualOverlap
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (hOverlap : noVirtualOverlap root)
    (hMap : root.mapPage vaddr paddr = some root') :
    noVirtualOverlap root' := by
  unfold mapPage at hMap
  cases hLookup : lookup root vaddr with
  | some _ => simp [hLookup] at hMap
  | none =>
      simp [hLookup] at hMap
      cases hMap
      intro v p₁ p₂ hIn₁ hIn₂
      simp [List.mem_cons] at hIn₁ hIn₂
      cases hIn₁ with
      | inl h₁ =>
        cases hIn₂ with
        | inl h₂ => rw [h₁.2, h₂.2]
        | inr h₂ =>
          exfalso
          exact lookup_eq_none_not_mem root _ p₂ hLookup (h₁.1 ▸ h₂)
      | inr h₁ =>
        cases hIn₂ with
        | inl h₂ =>
          exfalso
          exact lookup_eq_none_not_mem root _ p₁ hLookup (h₂.1 ▸ h₁)
        | inr h₂ => exact hOverlap v p₁ p₂ h₁ h₂

/-- F-08 helper: a successful `unmapPage` preserves the no-virtual-overlap invariant.
    Since `unmapPage` only removes entries, it cannot create new overlap. -/
theorem unmapPage_noVirtualOverlap
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (hOverlap : noVirtualOverlap root)
    (hUnmap : root.unmapPage vaddr = some root') :
    noVirtualOverlap root' := by
  unfold unmapPage at hUnmap
  cases hLookup : lookup root vaddr with
  | none => simp [hLookup] at hUnmap
  | some _ =>
      simp [hLookup] at hUnmap
      cases hUnmap
      intro v p₁ p₂ hIn₁ hIn₂
      simp [List.mem_filter] at hIn₁ hIn₂
      exact hOverlap v p₁ p₂ hIn₁.1 hIn₂.1

/-- TPI-001 helper: mapping vaddr does not affect lookup of a different vaddr'. -/
theorem lookup_mapPage_ne
    (root root' : VSpaceRoot)
    (vaddr vaddr' : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (hNe : vaddr ≠ vaddr')
    (hMap : root.mapPage vaddr paddr = some root') :
    root'.lookup vaddr' = root.lookup vaddr' := by
  unfold mapPage at hMap
  cases hLookup : lookup root vaddr with
  | some _ => simp [hLookup] at hMap
  | none =>
      simp [hLookup] at hMap
      cases hMap
      unfold lookup
      simp [hNe]

/-- TPI-001 helper: unmapPage at vaddr does not affect lookup of a different vaddr'. -/
theorem lookup_unmapPage_ne
    (root root' : VSpaceRoot)
    (vaddr vaddr' : SeLe4n.VAddr)
    (hNe : vaddr ≠ vaddr')
    (hUnmap : root.unmapPage vaddr = some root') :
    root'.lookup vaddr' = root.lookup vaddr' := by
  unfold unmapPage at hUnmap
  cases hLookup : lookup root vaddr with
  | none => simp [hLookup] at hUnmap
  | some _ =>
      simp [hLookup] at hUnmap
      cases hUnmap
      unfold lookup
      simp only
      congr 1
      rw [List.find?_filter]
      congr 1
      funext x
      by_cases hx : x.fst = vaddr'
      · simp [hx, Ne.symm hNe]
      · simp [hx]

end VSpaceRoot

namespace CNode

inductive ResolveError where
  | depthMismatch
  | guardMismatch
  deriving Repr, DecidableEq

def empty : CNode :=
  { guard := 0, radix := 0, slots := [] }

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

def lookup (node : CNode) (slot : SeLe4n.Slot) : Option Capability :=
  (node.slots.find? (fun entry => entry.fst = slot)).map Prod.snd

def insert (node : CNode) (slot : SeLe4n.Slot) (cap : Capability) : CNode :=
  let slots := (slot, cap) :: node.slots.filter (fun entry => entry.fst ≠ slot)
  { node with slots }

def remove (node : CNode) (slot : SeLe4n.Slot) : CNode :=
  { node with slots := node.slots.filter (fun entry => entry.fst ≠ slot) }

/-- Local revoke helper for the current modeled slice.

This keeps the authority-bearing source slot while deleting sibling slots in the same CNode that
name the same capability target. Full cross-CNode revoke requires an explicit derivation graph and
is intentionally deferred. -/
def revokeTargetLocal (node : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget) : CNode :=
  {
    node with
      slots := node.slots.filter (fun entry => entry.fst = sourceSlot ∨ entry.snd.target ≠ target)
  }

theorem lookup_remove_eq_none (node : CNode) (slot : SeLe4n.Slot) :
    (node.remove slot).lookup slot = none := by
  unfold remove lookup
  simp

theorem resolveSlot_depthMismatch
    (node : CNode)
    (cptr : SeLe4n.CPtr)
    (depth : Nat)
    (hDepth : depth < node.radix) :
    node.resolveSlot cptr depth = .error .depthMismatch := by
  unfold resolveSlot
  simp [hDepth]

theorem lookup_revokeTargetLocal_source_eq_lookup
    (node : CNode)
    (sourceSlot : SeLe4n.Slot)
    (target : CapTarget) :
    (node.revokeTargetLocal sourceSlot target).lookup sourceSlot = node.lookup sourceSlot := by
  unfold revokeTargetLocal lookup
  have hPred :
      (fun entry : SeLe4n.Slot × Capability =>
        (decide (entry.fst = sourceSlot) || !decide (entry.snd.target = target)) &&
          decide (entry.fst = sourceSlot)) =
      (fun entry : SeLe4n.Slot × Capability => decide (entry.fst = sourceSlot)) := by
    funext entry
    by_cases hEq : entry.fst = sourceSlot <;> simp [hEq]
  simp [hPred]

-- ============================================================================
-- WS-E2 / C-01: Non-trivial CNode slot-index uniqueness infrastructure
-- ============================================================================

/-- CNode slot-index uniqueness: each slot index maps to at most one capability
in the slot list. This is a non-trivial structural invariant maintained by CNode
operations (insert removes duplicates before prepending, remove/revoke only filter).

WS-E2 / C-01 remediation: replaces the prior tautological definition that merely
proved a pure function returns the same output for the same input. -/
def slotsUnique (cn : CNode) : Prop :=
  ∀ slot cap₁ cap₂,
    (slot, cap₁) ∈ cn.slots →
    (slot, cap₂) ∈ cn.slots →
    cap₁ = cap₂

theorem empty_slotsUnique : CNode.empty.slotsUnique := by
  intro slot cap₁ cap₂ h₁
  simp [CNode.empty] at h₁

/-- `insert` preserves slot-key uniqueness: the old entry for `slot` is filtered out
before prepending the new one, so no duplicate keys are introduced. -/
theorem insert_slotsUnique
    (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (hUniq : cn.slotsUnique) :
    (cn.insert slot cap).slotsUnique := by
  intro s c₁ c₂ h₁ h₂
  simp only [insert, List.mem_cons, List.mem_filter] at h₁ h₂
  rcases h₁ with h₁eq | ⟨h₁m, h₁p⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₁eq
    rcases h₂ with h₂eq | ⟨h₂m, h₂p⟩
    · exact (Prod.mk.inj h₂eq).2.symm
    · exfalso; simp at h₂p
  · rcases h₂ with h₂eq | ⟨h₂m, h₂p⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₂eq
      exfalso; simp at h₁p
    · exact hUniq s c₁ c₂ h₁m h₂m

/-- `remove` preserves slot-key uniqueness: filtering can only reduce the slot list. -/
theorem remove_slotsUnique
    (cn : CNode) (slot : SeLe4n.Slot)
    (hUniq : cn.slotsUnique) :
    (cn.remove slot).slotsUnique := by
  intro s c₁ c₂ h₁ h₂
  simp only [remove, List.mem_filter] at h₁ h₂
  exact hUniq s c₁ c₂ h₁.1 h₂.1

/-- `revokeTargetLocal` preserves slot-key uniqueness: it is a filter operation
that can only reduce the slot list. -/
theorem revokeTargetLocal_slotsUnique
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (hUniq : cn.slotsUnique) :
    (cn.revokeTargetLocal sourceSlot target).slotsUnique := by
  intro s c₁ c₂ h₁ h₂
  simp only [revokeTargetLocal, List.mem_filter] at h₁ h₂
  exact hUniq s c₁ c₂ h₁.1 h₂.1

/-- Soundness of `lookup`: a successful lookup witnesses membership in the slot list. -/
theorem lookup_mem_of_some
    (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (hLookup : cn.lookup slot = some cap) :
    (slot, cap) ∈ cn.slots := by
  unfold lookup at hLookup
  cases hFind : cn.slots.find? (fun entry => decide (entry.fst = slot)) with
  | none => simp [hFind] at hLookup
  | some entry =>
    simp [hFind] at hLookup
    have hSlot : entry.fst = slot := by simpa using List.find?_some hFind
    have hMem := List.mem_of_find?_eq_some hFind
    rw [← hLookup, ← hSlot]
    exact (Prod.eta entry) ▸ hMem

/-- Completeness of `lookup` under slot-index uniqueness: every slot list member is
retrievable. This is non-trivial — it fails when duplicate slot indices exist,
because `find?` returns only the first match. (WS-E2 / C-01) -/
theorem mem_lookup_of_slotsUnique
    (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (hUniq : cn.slotsUnique)
    (hMem : (slot, cap) ∈ cn.slots) :
    cn.lookup slot = some cap := by
  unfold lookup
  cases hFind : cn.slots.find? (fun entry => decide (entry.fst = slot)) with
  | none =>
    exfalso
    have := (List.find?_eq_none.mp hFind) ⟨slot, cap⟩ hMem
    simp at this
  | some entry =>
    simp
    have hSlot : entry.fst = slot := by simpa using List.find?_some hFind
    have hEntryMem := List.mem_of_find?_eq_some hFind
    have hRewrite : (slot, entry.snd) ∈ cn.slots := by
      rw [← hSlot]; exact (Prod.eta entry) ▸ hEntryMem
    exact hUniq slot entry.snd cap hRewrite hMem

end CNode

inductive KernelObject where
  | tcb (t : TCB)
  | endpoint (e : Endpoint)
  | notification (n : Notification)
  | cnode (c : CNode)
  | vspaceRoot (v : VSpaceRoot)
  deriving Repr, DecidableEq

inductive KernelObjectType where
  | tcb
  | endpoint
  | notification
  | cnode
  | vspaceRoot
  deriving Repr, DecidableEq

namespace KernelObject

def objectType : KernelObject → KernelObjectType
  | .tcb _ => .tcb
  | .endpoint _ => .endpoint
  | .notification _ => .notification
  | .cnode _ => .cnode
  | .vspaceRoot _ => .vspaceRoot

end KernelObject

/-- Construct a capability that names an object directly. -/
def makeObjectCap (id : SeLe4n.ObjId) (rights : List AccessRight) : Capability :=
  { target := .object id, rights }

end SeLe4n.Model
