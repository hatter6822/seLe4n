-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.Architecture.IpcBufferRead
import SeLe4n.Kernel.Architecture.HardwareTables

/-! # IPC Capability Transfer (seL4's `transferCaps`)

During an IPC send or call, the capabilities the sender's frame names are
resolved in the sender's CSpace at the rendezvous (`resolveExtraCaps`, seL4's
`lookupExtraCaps`), and the resulting transient array is transferred to the
receiver in the same step.  No resolved capability is ever stored in a message
or a thread: `IpcMessage` has no capability field.

**seL4 semantics** (`transferCaps`, `transferCapsToSlots`):
- The receiver names **one** receive slot, in its IPC buffer's receive path
  (`receiveCNode`, `receiveIndex`, `receiveDepth`; seL4's
  `seL4_SetCapReceivePath`), resolved at the transfer (`receiveSlot?`, seL4's
  `getReceiveSlots`).  A path that does not resolve to an empty slot names
  none.
- A receiver with no IPC buffer the kernel may write receives nothing.
- The capabilities are processed in order.  One to the endpoint the message
  was sent on is **unwrapped**: its badge is written to the receiver's
  `caps_or_badges` word at its index and its bit set in `capsUnwrapped`; no
  capability is installed.  Any other is derived and installed in the receive
  slot (`ipcTransferSingleCap`), which is then used up.
- The transfer **stops** at the first capability it can neither unwrap nor
  install — no receive slot, or one already used, or a derivation seL4 refuses
  — with no fault.  What it already transferred stays.
- The report (`CapTransferSummary.capInfo`) is the number of capabilities
  processed and which were unwrapped; the receiver's `MessageInfo` carries it.
- The sender keeps every capability (IPC transfer is a copy).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

open SeLe4n.Kernel.Architecture.IpcBufferRead in
/-- A word of a thread's IPC buffer, as the kernel reads it there (the entry's
words ahead of the model's memory, `userWordAt`); `none` where the buffer does
not resolve. -/
@[inline] def receiverBufferWord? (st : SystemState) (tcb : TCB) (idx : Nat) : Option UInt64 :=
  (ipcBufferWordPAddr? st tcb idx false).map (userWordAt st.machine)

open SeLe4n.Kernel.Architecture.IpcBufferRead in
/-- **The receiver has an IPC buffer the kernel may write** (seL4's
`lookupIPCBuffer(true, receiver)` answering a buffer): its first word resolves
writable through its own VSpace.  The buffer lies in one frame
(`ipcBufferWords_within_alignment`), so its other words resolve through the same
mapping. -/
@[inline] def receiverHasBuffer (st : SystemState) (tcb : TCB) : Bool :=
  (ipcBufferWordPAddr? st tcb 0 true).isSome

/-- **The slot a receive path names** (seL4's `getReceiveSlots`): the
`receiveCNode` word looked up in the receiver's CSpace (`lookupCap`) must name a
CNode, in which `receiveIndex` resolves `receiveDepth` bits deep (seL4's
`lookupTargetSlot`, a depth from 1 to the word's 64 bits) to a slot that is
empty.  Any failure names no slot, and a transfer then installs nothing; seL4
raises no fault for it. -/
def receivePathSlot? (st : SystemState) (tcb : TCB) (cnodeWord indexWord depthWord : UInt64) :
    Option CSpaceAddr :=
  match st.getCNode? tcb.cspaceRoot with
  | none => none
  | some rootCn =>
    match resolveCapAddress tcb.cspaceRoot (SeLe4n.CPtr.ofWord cnodeWord) rootCn.depth st with
    | .error _ => none
    | .ok ref =>
      match SystemState.lookupSlotCap st ref with
      | none => none
      | some cap =>
        match cap.target with
        | .object cnodeId =>
          match st.getCNode? cnodeId with
          | none => none
          | some _ =>
            if depthWord.toNat = 0 ∨ 64 < depthWord.toNat then none else
            match resolveCapAddress cnodeId (SeLe4n.CPtr.ofWord indexWord) depthWord.toNat st with
            | .error _ => none
            | .ok slot =>
              if (SystemState.lookupSlotCap st slot).isNone then some slot else none
        | _ => none

open SeLe4n.Kernel.Architecture.IpcBufferRead in
/-- **The receiver's receive slot** (seL4's `getReceiveSlots`): the slot its
IPC buffer's receive path names, read from the buffer at the transfer. -/
def receiveSlot? (st : SystemState) (tcb : TCB) : Option CSpaceAddr :=
  match receiverBufferWord? st tcb ipcBufferReceiveCNodeWord,
      receiverBufferWord? st tcb ipcBufferReceiveIndexWord,
      receiverBufferWord? st tcb ipcBufferReceiveDepthWord with
  | some c, some i, some d => receivePathSlot? st tcb c i d
  | _, _, _ => none

/-- **A capability the transfer unwraps**: one to the endpoint the message was
sent on (seL4: an endpoint capability whose object is that endpoint).  Only its
badge is delivered.  A reply is sent on no endpoint (seL4's `doReplyTransfer`
passes `NULL` to `doIPCTransfer`), so it unwraps nothing. -/
@[inline] def capUnwrapsAt (cap : Capability) (endpointId : Option SeLe4n.ObjId) : Bool :=
  match cap.target, endpointId with
  | .object id, some ep => id == ep
  | _, _ => false

open SeLe4n.Kernel.Architecture.IpcBufferRead in
/-- **The badge an unwrapped capability delivers, written to the receiver's
`caps_or_badges` word at its index** (seL4's `setExtraBadge`), into the ledger
of the physical writes the step makes.  The word is in the receiver's buffer,
which the transfer checked the kernel may write (`receiverHasBuffer`). -/
def recordUnwrappedBadge (st : SystemState) (tcb : TCB) (i : Nat) (badge : SeLe4n.Badge) :
    SystemState :=
  match ipcBufferWordPAddr? st tcb (ipcBufferCapsOrBadgesWord i) true with
  | some pa => Architecture.recordPhysicalWrites st [.storeUserWord pa badge.word]
  | none => st

@[simp] theorem recordUnwrappedBadge_objects (st : SystemState) (tcb : TCB) (i : Nat)
    (b : SeLe4n.Badge) : (recordUnwrappedBadge st tcb i b).objects = st.objects := by
  unfold recordUnwrappedBadge; split <;> rfl

/-- The badge record writes none of the bookkeeping ghosts. -/
theorem recordUnwrappedBadge_ghostsKept (st : SystemState) (tcb : TCB) (i : Nat)
    (b : SeLe4n.Badge) : SystemState.ghostsKept (recordUnwrappedBadge st tcb i b) st := by
  unfold recordUnwrappedBadge; split <;> exact ⟨rfl, rfl, rfl⟩

@[simp] theorem recordUnwrappedBadge_scheduler (st : SystemState) (tcb : TCB) (i : Nat)
    (b : SeLe4n.Badge) : (recordUnwrappedBadge st tcb i b).scheduler = st.scheduler := by
  unfold recordUnwrappedBadge; split <;> rfl

@[simp] theorem recordUnwrappedBadge_machine (st : SystemState) (tcb : TCB) (i : Nat)
    (b : SeLe4n.Badge) : (recordUnwrappedBadge st tcb i b).machine = st.machine := by
  unfold recordUnwrappedBadge; split <;> rfl

@[simp] theorem recordUnwrappedBadge_cdt (st : SystemState) (tcb : TCB) (i : Nat)
    (b : SeLe4n.Badge) : (recordUnwrappedBadge st tcb i b).cdt = st.cdt := by
  unfold recordUnwrappedBadge; split <;> rfl

/-- **One capability's turn of seL4's `transferCapsToSlots` loop**, from index
`idx`: unwrap a capability to the endpoint (its badge to the receiver's buffer),
or install it in the receive slot `slot?` and use the slot up, or stop.
Termination is structural on `fuel` (`caps.size` at the entry). -/
def ipcUnwrapCapsLoop (caps : Array TransferCap) (endpointId : Option SeLe4n.ObjId) (rtcb : TCB)
    (idx : Nat) (slot? : Option CSpaceAddr) (acc : Array CapTransferResult) (fuel : Nat) :
    Kernel CapTransferSummary :=
  match fuel with
  | 0 => fun st => .ok ({ results := acc }, st)
  | fuel' + 1 =>
    match caps[idx]? with
    | none => fun st => .ok ({ results := acc }, st)
    | some tc => fun st =>
      if capUnwrapsAt tc.cap endpointId then
        let b := tc.cap.badge.getD SeLe4n.Badge.zero
        ipcUnwrapCapsLoop caps endpointId rtcb (idx + 1) slot? (acc.push (.unwrapped b)) fuel'
          (recordUnwrappedBadge st rtcb idx b)
      else
        match slot? with
        | none => .ok ({ results := acc }, st)
        | some dst =>
          match ipcTransferSingleCap tc.cap tc.srcSlot dst st with
          | .error _ => .ok ({ results := acc }, st)
          | .ok ((), st') =>
            ipcUnwrapCapsLoop caps endpointId rtcb (idx + 1) none
              (acc.push (.installed dst.cnode dst.slot)) fuel' st'

/-- **Transfer the capabilities resolved at the rendezvous** (seL4's
`transferCapsToSlots`) to the receiver `rtcb`, whose receive slot is `slot?`,
for a message sent on `endpointId`. -/
def ipcUnwrapCaps (caps : Array TransferCap) (endpointId : Option SeLe4n.ObjId) (rtcb : TCB)
    (slot? : Option CSpaceAddr) : Kernel CapTransferSummary :=
  ipcUnwrapCapsLoop caps endpointId rtcb 0 slot? #[] caps.size

/-- **The loop's frame, once for every relation it is stated for**: a relation
between post- and pre-state that is reflexive and transitive, that a badge write
satisfies, and that an install into the receive slot satisfies, relates the
loop's result to its start. -/
theorem ipcUnwrapCapsLoop_rel (R : SystemState → SystemState → Prop)
    (hRefl : ∀ s, R s s) (hTrans : ∀ a b c, R c b → R b a → R c a)
    (caps : Array TransferCap) (endpointId : Option SeLe4n.ObjId) (rtcb : TCB)
    (hBadge : ∀ s i b, R (recordUnwrappedBadge s rtcb i b) s) :
    ∀ (fuel idx : Nat) (slot? : Option CSpaceAddr) (acc : Array CapTransferResult)
      (st st' : SystemState) (summary : CapTransferSummary),
      (∀ dst s s' (tc : TransferCap), slot? = some dst → (∃ i : Nat, caps[i]? = some tc) →
        ipcTransferSingleCap tc.cap tc.srcSlot dst s = .ok ((), s') → R s' s) →
      ipcUnwrapCapsLoop caps endpointId rtcb idx slot? acc fuel st = .ok (summary, st') →
      R st' st
  | 0, _, _, _, st, st', _, _, h => by
    simp only [ipcUnwrapCapsLoop, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact hRefl st
  | fuel + 1, idx, slot?, acc, st, st', summary, hInst, h => by
    simp only [ipcUnwrapCapsLoop] at h
    cases hC : caps[idx]? with
    | none =>
      simp only [hC, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact hRefl st
    | some tc =>
      simp only [hC] at h
      split at h
      · exact hTrans _ _ _
          (ipcUnwrapCapsLoop_rel R hRefl hTrans caps endpointId rtcb hBadge fuel _ _ _ _ _ _
            hInst h) (hBadge _ _ _)
      · cases hS : slot? with
        | none =>
          simp only [hS, Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.2]; exact hRefl st
        | some dst =>
          simp only [hS] at h
          cases hT : ipcTransferSingleCap tc.cap tc.srcSlot dst st with
          | error e =>
            simp only [hT, Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.2]; exact hRefl st
          | ok pair =>
            obtain ⟨⟨⟩, sI⟩ := pair
            simp only [hT] at h
            exact hTrans _ _ _
              (ipcUnwrapCapsLoop_rel R hRefl hTrans caps endpointId rtcb hBadge fuel _ none _ _ _ _
                (fun _ _ _ _ hN => by cases hN) h)
              (hInst dst st sI tc hS ⟨idx, hC⟩ hT)

/-- `ipcUnwrapCapsLoop_rel` at the entry. -/
theorem ipcUnwrapCaps_rel (R : SystemState → SystemState → Prop)
    (hRefl : ∀ s, R s s) (hTrans : ∀ a b c, R c b → R b a → R c a)
    {caps : Array TransferCap} {endpointId : Option SeLe4n.ObjId} {rtcb : TCB}
    {slot? : Option CSpaceAddr} {st st' : SystemState} {summary : CapTransferSummary}
    (hBadge : ∀ s i b, R (recordUnwrappedBadge s rtcb i b) s)
    (hInst : ∀ dst s s' (tc : TransferCap), slot? = some dst → (∃ i : Nat, caps[i]? = some tc) →
      ipcTransferSingleCap tc.cap tc.srcSlot dst s = .ok ((), s') → R s' s)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st')) : R st' st :=
  ipcUnwrapCapsLoop_rel R hRefl hTrans caps endpointId rtcb hBadge _ _ _ _ _ _ _ hInst h

theorem ipcUnwrapCaps_preserves_scheduler (caps : Array TransferCap)
    (endpointId : Option SeLe4n.ObjId) (rtcb : TCB) (slot? : Option CSpaceAddr)
    (st st' : SystemState) (summary : CapTransferSummary)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st')) :
    st'.scheduler = st.scheduler :=
  ipcUnwrapCaps_rel (fun a b => a.scheduler = b.scheduler) (fun _ => rfl)
    (fun _ _ _ h1 h2 => h1.trans h2) (fun _ _ _ => recordUnwrappedBadge_scheduler _ _ _ _)
    (fun _ _ _ _ _ _ hT => ipcTransferSingleCap_preserves_scheduler _ _ _ _ _ hT) h

/-- WS-SM SM8.B.2: the transfer never touches the machine, so no core's banked
`RegisterFile` moves: a badge goes to the write ledger, an install to a CNode. -/
theorem ipcUnwrapCaps_preserves_machine (caps : Array TransferCap)
    (endpointId : Option SeLe4n.ObjId) (rtcb : TCB) (slot? : Option CSpaceAddr)
    (st st' : SystemState) (summary : CapTransferSummary)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st')) :
    st'.machine = st.machine :=
  ipcUnwrapCaps_rel (fun a b => a.machine = b.machine) (fun _ => rfl)
    (fun _ _ _ h1 h2 => h1.trans h2) (fun _ _ _ => recordUnwrappedBadge_machine _ _ _ _)
    (fun _ _ _ _ _ _ hT => ipcTransferSingleCap_preserves_machine _ _ _ _ _ hT) h

/-- WS-RR RR2.6: the transfer preserves the object store's extended invariant. -/
theorem ipcUnwrapCaps_preserves_objects_invExt (caps : Array TransferCap)
    (endpointId : Option SeLe4n.ObjId) (rtcb : TCB) (slot? : Option CSpaceAddr)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st')) :
    st'.objects.invExt :=
  ipcUnwrapCaps_rel (fun a b => b.objects.invExt → a.objects.invExt) (fun _ h => h)
    (fun _ _ _ h1 h2 hA => h1 (h2 hA))
    (fun _ _ _ hA => by rw [recordUnwrappedBadge_objects]; exact hA)
    (fun _ _ _ _ _ _ hT hA => ipcTransferSingleCap_preserves_objects_invExt _ _ _ _ _ hA hT)
    h hObjInv

/-- A CNode in the later state of a metadata agreement was a CNode before. -/
theorem agreeMeta_cnode_back {st st' : SystemState} {oid : SeLe4n.ObjId}
    (h : SystemState.objectAgreesOffDerivationMetadataAt st' st oid) {cn' : CNode}
    (h' : st'.objects[oid]? = some (.cnode cn')) : ∃ cn, st.objects[oid]? = some (.cnode cn) := by
  rcases h with e | ⟨cn, _, ha, _, _⟩ | ⟨_, _, _, hb, _⟩
  · exact ⟨cn', e ▸ h'⟩
  · exact ⟨cn, ha⟩
  · rw [hb] at h'; cases h'

/-- **What the transfer does to one object**: it holds the pre-state's object up
to derivation metadata, or it is the receive slot's CNode, a CNode before and
after.  Every per-object frame below is a corollary. -/
theorem ipcUnwrapCaps_object_cases (caps : Array TransferCap)
    (endpointId : Option SeLe4n.ObjId) (rtcb : TCB) (slot? : Option CSpaceAddr)
    (st st' : SystemState) (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st')) :
    SystemState.objectAgreesOffDerivationMetadataAt st' st oid ∨
      ∃ dst, slot? = some dst ∧ oid = dst.cnode ∧
        (∃ cn, st.objects[oid]? = some (.cnode cn)) ∧
        ∃ cn', st'.objects[oid]? = some (.cnode cn') := by
  let P : SystemState → SystemState → Prop := fun a b =>
    b.objects.invExt → a.objects.invExt ∧
      (SystemState.objectAgreesOffDerivationMetadataAt a b oid ∨
        ∃ dst, slot? = some dst ∧ oid = dst.cnode ∧
          (∃ cn, b.objects[oid]? = some (.cnode cn)) ∧
          ∃ cn', a.objects[oid]? = some (.cnode cn'))
  have hP : P st' st := by
    refine ipcUnwrapCaps_rel P (fun _ hI => ⟨hI, .inl (.of_eq rfl)⟩) ?_ ?_ ?_ h
    · intro a b c h1 h2 hA
      obtain ⟨hB, r2⟩ := h2 hA
      obtain ⟨hC, r1⟩ := h1 hB
      refine ⟨hC, ?_⟩
      rcases r1 with r1 | ⟨d1, hd1, ho1, ⟨cnB, hcnB⟩, ⟨cnC, hcnC⟩⟩ <;>
        rcases r2 with r2 | ⟨d2, hd2, ho2, ⟨cnA, hcnA⟩, ⟨cnB2, hcnB2⟩⟩
      · exact .inl (r1.trans r2)
      · obtain ⟨c', hc', -⟩ := r1.cnode_fwd hcnB2
        exact .inr ⟨d2, hd2, ho2, ⟨cnA, hcnA⟩, c', hc'⟩
      · exact .inr ⟨d1, hd1, ho1, agreeMeta_cnode_back r2 hcnB, cnC, hcnC⟩
      · exact .inr ⟨d2, hd2, ho2, ⟨cnA, hcnA⟩, cnC, hcnC⟩
    · intro s i b hA
      exact ⟨by rw [recordUnwrappedBadge_objects]; exact hA,
        .inl (.of_eq (by rw [recordUnwrappedBadge_objects]))⟩
    · intro dst s s' tc hS _ hT hA
      refine ⟨ipcTransferSingleCap_preserves_objects_invExt _ _ _ _ _ hA hT, ?_⟩
      by_cases hEq : oid = dst.cnode
      · subst hEq
        obtain ⟨cn, hCn⟩ := ipcTransferSingleCap_ok_implies_cnode_at_dst _ _ _ _ _ hT
        exact .inr ⟨dst, hS, rfl, ⟨cn, hCn⟩,
          ipcTransferSingleCap_dst_stays_cnode _ _ _ _ _ hA hT⟩
      · exact .inl (ipcTransferSingleCap_preserves_objects_ne _ _ _ _ _ oid hEq hA hT)
  exact (hP hObjInv).2

/-- The transfer holds every object other than the receive slot's CNode up to
derivation metadata. -/
theorem ipcUnwrapCaps_preserves_objects_ne (caps : Array TransferCap)
    (endpointId : Option SeLe4n.ObjId) (rtcb : TCB) (slot? : Option CSpaceAddr)
    (st st' : SystemState) (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    (hNe : ∀ dst, slot? = some dst → oid ≠ dst.cnode) (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st')) :
    SystemState.objectAgreesOffDerivationMetadataAt st' st oid := by
  rcases ipcUnwrapCaps_object_cases _ _ _ _ _ _ _ oid hObjInv h with h1 | ⟨dst, hS, hO, -⟩
  · exact h1
  · exact absurd hO (hNe dst hS)

/-- **An object that is not a CNode survives the transfer**: the transfer
writes the receive slot's CNode, and every other object up to derivation
metadata, which only CNodes and threads carry. -/
theorem ipcUnwrapCaps_preserves_nonCNode (caps : Array TransferCap)
    (endpointId : Option SeLe4n.ObjId) (rtcb : TCB) (slot? : Option CSpaceAddr)
    (st st' : SystemState) (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    {o : KernelObject} (hNotCn : ∀ cn, o ≠ .cnode cn) (hNoMeta : ∀ t, o ≠ .tcb t)
    (hO : st.objects[oid]? = some o) (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st')) :
    st'.objects[oid]? = some o := by
  rcases ipcUnwrapCaps_object_cases _ _ _ _ _ _ _ oid hObjInv h with h1 | ⟨_, -, -, ⟨cn, hCn⟩, -⟩
  · exact h1.obj_fwd hO hNotCn hNoMeta
  · rw [hO] at hCn; exact absurd (Option.some.inj hCn) (hNotCn cn)

/-- And back: a non-CNode object after the transfer was there before. -/
theorem ipcUnwrapCaps_nonCNode_backward (caps : Array TransferCap)
    (endpointId : Option SeLe4n.ObjId) (rtcb : TCB) (slot? : Option CSpaceAddr)
    (st st' : SystemState) (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    {o : KernelObject} (hNotCn : ∀ cn, o ≠ .cnode cn) (hNoMeta : ∀ t, o ≠ .tcb t)
    (hO : st'.objects[oid]? = some o) (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st')) :
    st.objects[oid]? = some o := by
  rcases ipcUnwrapCaps_object_cases _ _ _ _ _ _ _ oid hObjInv h with h1 | ⟨_, -, -, -, ⟨cn, hCn⟩⟩
  · exact h1.obj_back hO hNotCn hNoMeta
  · rw [hO] at hCn; exact absurd (Option.some.inj hCn) (hNotCn cn)

theorem ipcUnwrapCaps_preserves_ntfn_objects (caps : Array TransferCap)
    (endpointId : Option SeLe4n.ObjId) (rtcb : TCB) (slot? : Option CSpaceAddr)
    (st st' : SystemState) (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    (ntfn : Notification) (hNtfn : st.objects[oid]? = some (.notification ntfn))
    (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st')) :
    st'.objects[oid]? = some (.notification ntfn) :=
  ipcUnwrapCaps_preserves_nonCNode _ _ _ _ _ _ _ oid (by intro _ e; cases e) (by intro _ e; cases e) hNtfn
    hObjInv h

theorem ipcUnwrapCaps_preserves_ep_objects (caps : Array TransferCap)
    (endpointId : Option SeLe4n.ObjId) (rtcb : TCB) (slot? : Option CSpaceAddr)
    (st st' : SystemState) (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    (ep : Endpoint) (hEp : st.objects[oid]? = some (.endpoint ep))
    (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st')) :
    st'.objects[oid]? = some (.endpoint ep) :=
  ipcUnwrapCaps_preserves_nonCNode _ _ _ _ _ _ _ oid (by intro _ e; cases e) (by intro _ e; cases e) hEp
    hObjInv h

theorem ipcUnwrapCaps_preserves_schedContext_objects (caps : Array TransferCap)
    (endpointId : Option SeLe4n.ObjId) (rtcb : TCB) (slot? : Option CSpaceAddr)
    (st st' : SystemState) (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    (sc : SchedContext) (hSc : st.objects[oid]? = some (.schedContext sc))
    (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st')) :
    st'.objects[oid]? = some (.schedContext sc) :=
  ipcUnwrapCaps_preserves_nonCNode _ _ _ _ _ _ _ oid (by intro _ e; cases e) (by intro _ e; cases e) hSc
    hObjInv h

theorem ipcUnwrapCaps_preserves_reply_objects (caps : Array TransferCap)
    (endpointId : Option SeLe4n.ObjId) (rtcb : TCB) (slot? : Option CSpaceAddr)
    (st st' : SystemState) (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    (r : SeLe4n.Kernel.Reply) (hR : st.objects[oid]? = some (.reply r))
    (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st')) :
    st'.objects[oid]? = some (.reply r) :=
  ipcUnwrapCaps_preserves_nonCNode _ _ _ _ _ _ _ oid (by intro _ e; cases e) (by intro _ e; cases e) hR
    hObjInv h

/-- IPC de-threading D4 Slice 2b: a post-state endpoint pulls back to the same
pre-state endpoint. -/
theorem ipcUnwrapCaps_endpoint_backward (caps : Array TransferCap)
    (endpointId : Option SeLe4n.ObjId) (rtcb : TCB) (slot? : Option CSpaceAddr)
    (st st' : SystemState) (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    (ep : Endpoint) (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st'))
    (hEp' : st'.objects[oid]? = some (.endpoint ep)) :
    st.objects[oid]? = some (.endpoint ep) :=
  ipcUnwrapCaps_nonCNode_backward _ _ _ _ _ _ _ oid (by intro _ e; cases e) (by intro _ e; cases e) hEp'
    hObjInv h

/-- A post-state notification was there before. -/
theorem ipcUnwrapCaps_ntfn_backward (caps : Array TransferCap)
    (endpointId : Option SeLe4n.ObjId) (rtcb : TCB) (slot? : Option CSpaceAddr)
    (st st' : SystemState) (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    (ntfn : Notification) (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st'))
    (hN' : st'.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) :=
  ipcUnwrapCaps_nonCNode_backward _ _ _ _ _ _ _ oid (by intro _ e; cases e) (by intro _ e; cases e) hN'
    hObjInv h

/-- A post-state scheduling context was there before. -/
theorem ipcUnwrapCaps_schedContext_backward (caps : Array TransferCap)
    (endpointId : Option SeLe4n.ObjId) (rtcb : TCB) (slot? : Option CSpaceAddr)
    (st st' : SystemState) (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    (sc : SchedContext) (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st'))
    (hS' : st'.objects[oid]? = some (.schedContext sc)) :
    st.objects[oid]? = some (.schedContext sc) :=
  ipcUnwrapCaps_nonCNode_backward _ _ _ _ _ _ _ oid (by intro _ e; cases e) (by intro _ e; cases e) hS'
    hObjInv h

/-- A post-state reply object was there before. -/
theorem ipcUnwrapCaps_reply_backward (caps : Array TransferCap)
    (endpointId : Option SeLe4n.ObjId) (rtcb : TCB) (slot? : Option CSpaceAddr)
    (st st' : SystemState) (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    (r : SeLe4n.Kernel.Reply) (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st'))
    (hR' : st'.objects[oid]? = some (.reply r)) :
    st.objects[oid]? = some (.reply r) :=
  ipcUnwrapCaps_nonCNode_backward _ _ _ _ _ _ _ oid (by intro _ e; cases e) (by intro _ e; cases e) hR'
    hObjInv h

/-- Every TCB survives the transfer off its space slots' derivation links. -/
theorem ipcUnwrapCaps_preserves_tcb_objects (caps : Array TransferCap)
    (endpointId : Option SeLe4n.ObjId) (rtcb : TCB) (slot? : Option CSpaceAddr)
    (st st' : SystemState) (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    (tcb : TCB) (hTcb : st.objects[oid]? = some (.tcb tcb)) (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st')) :
    ∃ tcb', st'.objects[oid]? = some (.tcb tcb') ∧ tcb'.withoutLinks = tcb.withoutLinks := by
  rcases ipcUnwrapCaps_object_cases _ _ _ _ _ _ _ oid hObjInv h with h1 | ⟨_, -, -, ⟨cn, hCn⟩, -⟩
  · exact h1.tcb_fwd hTcb
  · rw [hTcb] at hCn; cases hCn

/-- IPC de-threading D2: a TCB after the transfer was a TCB before, with the same
fields off its space slots' derivation links. -/
theorem ipcUnwrapCaps_tcb_backward (caps : Array TransferCap)
    (endpointId : Option SeLe4n.ObjId) (rtcb : TCB) (slot? : Option CSpaceAddr)
    (st st' : SystemState) (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    (tcb : TCB) (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st'))
    (hTcb' : st'.objects[oid]? = some (.tcb tcb)) :
    ∃ tcb₀, st.objects[oid]? = some (.tcb tcb₀) ∧ tcb.withoutLinks = tcb₀.withoutLinks := by
  rcases ipcUnwrapCaps_object_cases _ _ _ _ _ _ _ oid hObjInv h with h1 | ⟨_, -, -, -, ⟨cn, hCn⟩⟩
  · exact h1.tcb_back hTcb'
  · rw [hTcb'] at hCn; cases hCn

/-- **WS-RR RR8.12**: the transfer fixes the whole `getTcb?` projection off the
space slots' derivation links. -/
theorem ipcUnwrapCaps_getTcb?_eq (caps : Array TransferCap)
    (endpointId : Option SeLe4n.ObjId) (rtcb : TCB) (slot? : Option CSpaceAddr)
    (st st' : SystemState) (summary : CapTransferSummary) (x : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st')) :
    (st'.getTcb? x).map TCB.withoutLinks = (st.getTcb? x).map TCB.withoutLinks := by
  simp only [SystemState.getTcb?]
  cases hT' : st'.objects[x.toObjId]? with
  | some obj' =>
    cases obj' with
    | tcb tcb' =>
      obtain ⟨t0, h0, hw⟩ := ipcUnwrapCaps_tcb_backward _ _ _ _ _ _ _ x.toObjId tcb' hObjInv h hT'
      rw [h0]; simp only [Option.map_some, hw]
    | _ =>
      cases hT : st.objects[x.toObjId]? with
      | none => rfl
      | some obj =>
        cases obj with
        | tcb t =>
          obtain ⟨t', h', _⟩ := ipcUnwrapCaps_preserves_tcb_objects _ _ _ _ _ _ _ x.toObjId t hT hObjInv h
          rw [h'] at hT'; cases hT'
        | _ => rfl
  | none =>
    cases hT : st.objects[x.toObjId]? with
    | none => rfl
    | some obj =>
      cases obj with
      | tcb t =>
        obtain ⟨t', h', _⟩ := ipcUnwrapCaps_preserves_tcb_objects _ _ _ _ _ _ _ x.toObjId t hT hObjInv h
        rw [h'] at hT'; cases hT'
      | _ => rfl

/-- A transfer with no receive slot installs nothing: it unwraps or stops, and
writes no object. -/
theorem ipcUnwrapCaps_objects_of_noSlot {caps : Array TransferCap}
    {endpointId : Option SeLe4n.ObjId} {rtcb : TCB} {st st' : SystemState}
    {summary : CapTransferSummary}
    (h : ipcUnwrapCaps caps endpointId rtcb none st = .ok (summary, st')) :
    st'.objects = st.objects ∧ st'.cdt = st.cdt :=
  ipcUnwrapCaps_rel (fun a b => a.objects = b.objects ∧ a.cdt = b.cdt) (fun _ => ⟨rfl, rfl⟩)
    (fun _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩)
    (fun _ _ _ => ⟨recordUnwrappedBadge_objects _ _ _ _, recordUnwrappedBadge_cdt _ _ _ _⟩)
    (fun _ _ _ _ hN => by cases hN) h

end SeLe4n.Kernel
